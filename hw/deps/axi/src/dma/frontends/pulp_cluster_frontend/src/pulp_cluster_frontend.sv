// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Thomas Benz <tbenz@ethz.ch>

/// replaces the mchan in the pulp cluster if the new AXI DMA should be used
/// strictly 32 bit on the TCDM side.
module pulp_cluster_frontend #(
    /// number of cores in the cluster
    parameter int unsigned NumCores       = -1,
    /// id width of peripherals
    parameter int unsigned PerifIdWidth   = -1,
    /// id width of the DMA AXI Master port
    parameter int unsigned DmaAxiIdWidth  = -1,
    /// data width of the DMA AXI Master port
    parameter int unsigned DmaDataWidth   = -1,
    /// address width of the DMA AXI Master port
    parameter int unsigned DmaAddrWidth   = -1,
    /// number of AX requests in-flight
    parameter int unsigned AxiAxReqDepth  = -1,
    /// number of 1D transfers buffered in backend
    parameter int unsigned TfReqFifoDepth = -1,
    /// data request type
    parameter type axi_req_t      = logic,
    /// data response type
    parameter type axi_res_t      = logic,
    /// transfer descriptor for hw access to DMA
    parameter type transf_descr_t = logic
)(
    input  logic                      clk_i,
    input  logic                      rst_ni,
    input logic [5:0]                 cluster_id_i,
    /// x-bar
    input  logic                      ctrl_pe_targ_req_i,
    input  logic                      ctrl_pe_targ_type_i,
    input  logic [3:0]                ctrl_pe_targ_be_i,
    input  logic [31:0]               ctrl_pe_targ_add_i,
    input  logic [31:0]               ctrl_pe_targ_data_i,
    input  logic [PerifIdWidth-1:0]   ctrl_pe_targ_id_i,
    output logic                      ctrl_pe_targ_gnt_o,
    output logic                      ctrl_pe_targ_r_valid_o,
    output logic [31:0]               ctrl_pe_targ_r_data_o,
    output logic                      ctrl_pe_targ_r_opc_o,
    output logic [PerifIdWidth-1:0]   ctrl_pe_targ_r_id_o,
    /// from cores
    input  logic [NumCores-1:0]       ctrl_targ_req_i,
    input  logic [NumCores-1:0]       ctrl_targ_type_i,
    input  logic [NumCores-1:0][3:0]  ctrl_targ_be_i,
    input  logic [NumCores-1:0][31:0] ctrl_targ_add_i,
    input  logic [NumCores-1:0][31:0] ctrl_targ_data_i,
    output logic [NumCores-1:0]       ctrl_targ_gnt_o,
    output logic [NumCores-1:0]       ctrl_targ_r_valid_o,
    output logic [NumCores-1:0][31:0] ctrl_targ_r_data_o,
    /// direct hw port
    input  logic                      dma_req_valid_i,
    output logic                      dma_req_ready_o,
    input  transf_descr_t             dma_req_i,
    output logic                      dma_rsp_valid_o,
    /// wide AXI port
    output axi_req_t                  axi_dma_req_o,
    input  axi_res_t                  axi_dma_res_i,
    /// status signal
    output logic                      busy_o,
    /// events and interrupts (cores)
    output logic [NumCores-1:0]       term_event_o,
    output logic [NumCores-1:0]       term_irq_o,
    /// events and interrupts (peripherals)
    output logic                      term_event_pe_o,
    output logic                      term_irq_pe_o,
    /// events and interrupts (cores)
    output logic [NumCores-1:0]       no_req_pending_o
);

    // number of register sets in fe
    localparam int unsigned NumRegs  = NumCores + 1;

    // arbitration index width
    localparam int unsigned IdxWidth = (NumRegs + 1 > 32'd1) ? unsigned'($clog2(NumRegs + 1)) : 32'd1;

    // buffer depth
    localparam int unsigned BufferDepth = 3; // + 64;

    localparam int unsigned TfFifoDepth = TfReqFifoDepth + AxiAxReqDepth + BufferDepth + 1;

    // 1D burst request
    typedef logic [DmaAddrWidth-1 :0] addr_t;
    typedef logic [DmaAxiIdWidth-1:0] axi_id_t;
    typedef struct packed {
        axi_id_t            id;
        addr_t              src, dst, num_bytes;
        axi_pkg::cache_t    cache_src, cache_dst;
        axi_pkg::burst_t    burst_src, burst_dst;
        logic               decouple_rw;
        logic               deburst;
        logic               serialize;
    } burst_req_t;

    // debug only: logfile
    integer log_file;
    string  log_file_name;

    // rr input
    transf_descr_t [NumRegs-1:0] transf_descr;
    logic          [NumRegs-1:0] be_ready;
    logic          [NumRegs-1:0] be_valid;
    // rr output
    transf_descr_t               transf_descr_arb;
    logic                        be_ready_arb;
    logic                        be_valid_arb;
    // the index ob the chosen pe
    logic [IdxWidth-1:0]         pe_idx_arb;

    // burst request definition
    burst_req_t burst_req;

    // transaction id
    logic [31:0] next_id, done_id;

    // keep track of peripherals
    logic [PerifIdWidth-1:0] peripherals_id_q;

    // backend idle signal
    logic be_idle;
    logic trans_complete;

    // information about most recent transfer
    logic [IdxWidth-1:0] tf_head;
    logic                tf_empty;

    // define a counter to keep track of the cores individual requests
    localparam int unsigned MaxNumRequests = TfReqFifoDepth + BufferDepth + 1;
    localparam int unsigned MaxReqWidth = $clog2(MaxNumRequests);
    logic [NumCores-1:0][MaxReqWidth-1:0] core_tf_num_d, core_tf_num_q;

    // generate registers for cores
    for (genvar i = 0; i < NumCores; i++) begin : gen_core_regs

        pulp_cluster_frontend_regs #(
            .transf_descr_t ( transf_descr_t    )
        ) i_dma_conf_regs_cores (
            .clk_i          ( clk_i                   ),
            .rst_ni         ( rst_ni                  ),
            .ctrl_req_i     ( ctrl_targ_req_i     [i] ),
            .ctrl_type_i    ( ctrl_targ_type_i    [i] ),
            .ctrl_be_i      ( ctrl_targ_be_i      [i] ),
            .ctrl_add_i     ( ctrl_targ_add_i     [i] ),
            .ctrl_data_i    ( ctrl_targ_data_i    [i] ),
            .ctrl_gnt_o     ( ctrl_targ_gnt_o     [i] ),
            .ctrl_valid_o   ( ctrl_targ_r_valid_o [i] ),
            .ctrl_data_o    ( ctrl_targ_r_data_o  [i] ),
            .next_id_i      ( next_id                 ),
            .done_id_i      ( done_id                 ),
            .be_ready_i     ( be_ready            [i] ),
            .be_valid_o     ( be_valid            [i] ),
            .be_busy_i      ( busy_o                  ),
            .transf_descr_o ( transf_descr        [i] )
        );
    end // gen_core_regs

    // generate registers for cores
    for (genvar i = 0; i < NumCores; i++) begin : gen_req_counters
        //increase counter if tf is started
        always_comb begin : proc_counter
            // default
            core_tf_num_d[i] = core_tf_num_q[i];
            // increase
            if (be_ready[i] & be_valid[i] & transf_descr[i].num_bytes != 0) begin
                core_tf_num_d[i] = core_tf_num_d[i] + 1;
            end
            // decrement
            if ((tf_head == i) & !tf_empty & trans_complete) begin
                core_tf_num_d[i] = core_tf_num_d[i] - 1;
            end
        end
        // assign output
        assign no_req_pending_o[i] = core_tf_num_d[i] == 0;
    end // gen_req_counters

    // generate registers for peripherals
    pulp_cluster_frontend_regs #(
        .transf_descr_t ( transf_descr_t    )
    ) i_dma_conf_regs_periphs (
        .clk_i          ( clk_i                             ),
        .rst_ni         ( rst_ni                            ),
        .ctrl_req_i     ( ctrl_pe_targ_req_i                ),
        .ctrl_type_i    ( ctrl_pe_targ_type_i               ),
        .ctrl_be_i      ( ctrl_pe_targ_be_i                 ),
        .ctrl_add_i     ( ctrl_pe_targ_add_i                ),
        .ctrl_data_i    ( ctrl_pe_targ_data_i               ),
        .ctrl_gnt_o     ( ctrl_pe_targ_gnt_o                ),
        .ctrl_valid_o   ( ctrl_pe_targ_r_valid_o            ),
        .ctrl_data_o    ( ctrl_pe_targ_r_data_o             ),
        .next_id_i      ( next_id                           ),
        .done_id_i      ( done_id                           ),
        .be_ready_i     ( be_ready               [NumCores] ),
        .be_valid_o     ( be_valid               [NumCores] ),
        .be_busy_i      ( busy_o                            ),
        .transf_descr_o ( transf_descr           [NumCores] )
    );

    // set this to zero as it is done mchan
    assign ctrl_pe_targ_r_opc_o = 1'b0;

    // round robin to arbitrate
    rr_arb_tree #(
        .NumIn      ( NumRegs + 1      ), // +1 is the external unit
        .DataWidth  ( -1               ),
        .DataType   ( transf_descr_t   ),
        .ExtPrio    ( 0                ),
        .AxiVldRdy  ( 1                ),
        .LockIn     ( 1                )
    ) i_rr_arb_tree (
        .clk_i      ( clk_i                             ),
        .rst_ni     ( rst_ni                            ),
        .flush_i    ( 1'b0                              ),
        .rr_i       ( '0                                ),
        .req_i      ( { dma_req_valid_i, be_valid     } ),
        .gnt_o      ( { dma_req_ready_o, be_ready     } ),
        .data_i     ( { dma_req_i,       transf_descr } ),
        .gnt_i      ( be_ready_arb                      ),
        .req_o      ( be_valid_arb                      ),
        .data_o     ( transf_descr_arb                  ),
        .idx_o      ( pe_idx_arb                        )
    );

    // global transfer id
    transfer_id_gen #(
        // keep this fixed at 32 bit as two 32 bit counters are
        // relatively cheap
        .ID_WIDTH     ( 32     )
    ) i_transfer_id_gen (
        .clk_i        ( clk_i                                                         ),
        .rst_ni       ( rst_ni                                                        ),
        .issue_i      ( be_ready_arb & be_valid_arb & transf_descr_arb.num_bytes != 0 ),
        .retire_i     ( trans_complete                                                ),
        .next_o       ( next_id                                                       ),
        .completed_o  ( done_id                                                       )
    );

    // hold a bit for each launched transfer where it came from
    fifo_v3 #(
        .dtype     ( logic [IdxWidth-1:0]   ),
        .DEPTH     ( TfFifoDepth )
    ) i_tf_id_fifo (
        .clk_i     ( clk_i                                                         ),
        .rst_ni    ( rst_ni                                                        ),
        .flush_i   ( 1'b0                                                          ),
        .testmode_i( 1'b0                                                          ),
        .full_o    ( ),
        .empty_o   ( tf_empty                                                      ),
        .usage_o   ( ),
        .data_i    ( pe_idx_arb                                                    ), // we are external tf
        .push_i    ( be_ready_arb & be_valid_arb & transf_descr_arb.num_bytes != 0 ),
        .data_o    ( tf_head                                                       ),
        .pop_i     ( trans_complete                                                )
    );

    assign dma_rsp_valid_o = (tf_head == NumRegs) & !tf_empty & trans_complete;
    //     ack external tf    tf came from ext       valid       we are done :)

    //---------NON SYNTHESIZABLE ---------------
    `ifndef VERILATOR
    //pragma translate_off
    // log dma transfers to disk
    initial begin
        @(posedge rst_ni);
        $sformat(log_file_name, "DMA_TRANSFERS_%2h.log", cluster_id_i);
        log_file = $fopen(log_file_name, "w");
        $fwrite(log_file, "queue_time pe_id tf_id src dst num_bytes launch_time completion_time\n");
        $fclose(log_file);
    end
    // datatype to store arbitrated tf
    typedef struct packed {
        longint queue_time;
        longint pe_id;
        longint next_id;
        longint src;
        longint dst;
        longint len;
    } queued_tf_t;
    // launch tf
    typedef struct packed {
        queued_tf_t queued_tf;
        longint     launch_time;
    } launched_tf_t;
    // create queued tf
    queued_tf_t queued_tf, queued_tf_head;
    // pack queued tf
    always_comb begin
        queued_tf.queue_time = $time();
        queued_tf.pe_id      = pe_idx_arb;
        queued_tf.next_id    = next_id;
        queued_tf.src        = transf_descr_arb.src_addr;
        queued_tf.dst        = transf_descr_arb.dst_addr;
        queued_tf.len        = transf_descr_arb.num_bytes;
    end
    // use a fifo to model queuing
    fifo_v3 #(
        .dtype     ( queued_tf_t        ),
        .DEPTH     ( TfReqFifoDepth     )
    ) i_queue_fifo (
        .clk_i     ( clk_i                            ),
        .rst_ni    ( rst_ni                           ),
        .flush_i   ( 1'b0                             ),
        .testmode_i( 1'b0                             ),
        .full_o    ( ),
        .empty_o   ( ),
        .usage_o   ( ),
        .data_i    ( queued_tf                        ),
        .push_i    ( be_valid_arb && be_ready_arb     ),
        .data_o    ( queued_tf_head                   ),
        .pop_i     ( i_axi_dma_backend.burst_req_pop  )
    );
    // launched tf
    launched_tf_t launched_tf, launched_tf_head;
    // pack launched tf
    always_comb begin
        launched_tf.queued_tf   = queued_tf_head;
        launched_tf.launch_time = $time();
    end
    // use a fifo to hold tf info while it goes through the backend
    fifo_v3 #(
        .dtype     ( launched_tf_t                   ),
        .DEPTH     ( AxiAxReqDepth + BufferDepth + 1 )
    ) i_launch_fifo (
        .clk_i     ( clk_i                            ),
        .rst_ni    ( rst_ni                           ),
        .flush_i   ( 1'b0                             ),
        .testmode_i( 1'b0                             ),
        .full_o    ( ),
        .empty_o   ( ),
        .usage_o   ( ),
        .data_i    ( launched_tf                      ),
        .push_i    ( i_axi_dma_backend.burst_req_pop  ),
        .data_o    ( launched_tf_head                 ),
        .pop_i     ( trans_complete                   )
    );
    // write info to file
    always @(posedge clk_i) begin
        #0;
        if(trans_complete) begin
            log_file = $fopen(log_file_name, "a");
            $fwrite(log_file, "%0d %0d %0d 0x%0x 0x%0x %0d %0d %0d\n",
                               launched_tf_head.queued_tf.queue_time, launched_tf_head.queued_tf.pe_id,
                               launched_tf_head.queued_tf.next_id, launched_tf_head.queued_tf.src,
                               launched_tf_head.queued_tf.dst, launched_tf_head.queued_tf.len,
                               launched_tf_head.launch_time, $time()
                    );
            $fclose(log_file);
        end
    end
    //pragma translate_on
    `endif
    //---------NON SYNTHESIZABLE ---------------

    // map arbitrated transfer descriptor onto generic burst request
    always_comb begin : proc_map_to_1D_burst
        burst_req             = '0;
        burst_req.src         =  transf_descr_arb.src_addr;
        burst_req.dst         =  transf_descr_arb.dst_addr;
        burst_req.num_bytes   =  transf_descr_arb.num_bytes;
        burst_req.burst_src   = axi_pkg::BURST_INCR;
        burst_req.burst_dst   = axi_pkg::BURST_INCR;
        burst_req.decouple_rw = transf_descr_arb.decouple;
        burst_req.deburst     = transf_descr_arb.deburst;
        burst_req.serialize   = transf_descr_arb.serialize;
    end

    // instantiate backend :)
    axi_dma_backend #(
        .DataWidth         ( DmaDataWidth    ),
        .AddrWidth         ( DmaAddrWidth    ),
        .IdWidth           ( DmaAxiIdWidth   ),
        .AxReqFifoDepth    ( AxiAxReqDepth   ),
        .TransFifoDepth    ( TfReqFifoDepth  ),
        .BufferDepth       ( BufferDepth     ), // minimal 3 for giving full performance
        .axi_req_t         ( axi_req_t       ),
        .axi_res_t         ( axi_res_t       ),
        .burst_req_t       ( burst_req_t     ),
        .DmaIdWidth        ( 6               ),
        .DmaTracing        ( 0               )
    ) i_axi_dma_backend (
        .clk_i            ( clk_i             ),
        .rst_ni           ( rst_ni            ),
        .dma_id_i         ( cluster_id_i      ),
        .axi_dma_req_o    ( axi_dma_req_o     ),
        .axi_dma_res_i    ( axi_dma_res_i     ),
        .burst_req_i      ( burst_req         ),
        .valid_i          ( be_valid_arb      ),
        .ready_o          ( be_ready_arb      ),
        .backend_idle_o   ( be_idle           ),
        .trans_complete_o ( trans_complete    )
    );

    // busy if not idle
    assign busy_o = ~be_idle;

    // interrupts and events (unconditionally)
    assign term_event_o    = trans_complete ? '1 : '0;
    assign term_irq_o      = trans_complete ? '1 : '0;
    assign term_event_pe_o = trans_complete ? '1 : '0;
    assign term_irq_pe_o   = trans_complete ? '1 : '0;

    // keep id for peripherals
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_id_peripherals
        if(~rst_ni) begin
            peripherals_id_q <= 0;
            core_tf_num_q    <= 0;
        end else begin
            peripherals_id_q <= ctrl_pe_targ_id_i;
            core_tf_num_q    <= core_tf_num_d;
        end
    end

    // id is returned
    assign ctrl_pe_targ_r_id_o = peripherals_id_q;

endmodule : pulp_cluster_frontend
