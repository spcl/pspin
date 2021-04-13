// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module host_direct #(
    parameter int unsigned AW_FIFO_DEPTH        = 16,
    parameter int unsigned AR_FIFO_DEPTH        = 16,
    parameter int unsigned W_FIFO_DEPTH         = 16,
    parameter int unsigned WRITES_FIFO_DEPTH    = 32,
    parameter int unsigned READS_FIFO_DEPTH     = 32,
    parameter int unsigned AXI_AW               = 64,
    parameter int unsigned AXI_DW               = 512,
    parameter int unsigned CMD_IMM_DATA_SIZE    = 512,

    parameter type axi_host_aw_t                = logic,
    parameter type axi_host_ar_t                = logic,
    parameter type axi_host_w_t                 = logic,
    parameter type axi_host_r_t                 = logic,
    parameter type axi_host_b_t                 = logic,

    /// host data request type (64 bit)
    parameter type axi_host_req_t               = logic,
    /// host data response type (64 bit)
    parameter type axi_host_res_t               = logic,

    parameter type cmd_req_t                    = logic,
    parameter type cmd_res_t                    = logic,
    parameter type cmd_id_t                     = logic
) (
    input  logic             clk_i,
    input  logic             rst_ni,

    //command
    input  logic             cmd_req_valid_i,
    output logic             cmd_req_ready_o,
    input  cmd_req_t         cmd_req_i,

    //response
    output logic             cmd_resp_valid_o,
    output cmd_res_t         cmd_resp_o,

    /// to host (64 bit address)
    output axi_host_req_t    host_req_o,
    input  axi_host_res_t    host_resp_i
);

    localparam int unsigned BaseHDId = 'h11;
    localparam int unsigned CMD_IMM_DATA_BYTES = CMD_IMM_DATA_SIZE/8;
    localparam int unsigned AXI_STRB = AXI_DW/8;
    localparam int unsigned AXI_STRB_PADDING = AXI_STRB - CMD_IMM_DATA_BYTES;

    typedef struct packed {
        logic [AXI_AW-1:0]  address;
    } ax_descr_t;

    typedef struct packed {
        logic [CMD_IMM_DATA_SIZE-1:0]  data;
        logic [AXI_STRB-1:0] strb;
    } w_descr_t;

    logic fifo_aw_full, fifo_aw_push, fifo_aw_pop, fifo_aw_empty;
    logic fifo_w_full, fifo_w_push, fifo_w_pop, fifo_w_empty; 
    logic fifo_ar_full, fifo_ar_push, fifo_ar_pop, fifo_ar_empty;

    logic fifo_write_id_full, fifo_write_id_empty, fifo_write_id_push, fifo_write_id_pop;
    logic fifo_read_id_full, fifo_read_id_empty, fifo_read_id_push, fifo_read_id_pop;
    cmd_id_t fifo_write_id_out, fifo_read_id_out;

    ax_descr_t fifo_ax_data_in;
    ax_descr_t fifo_aw_data_out, fifo_ar_data_out;

    w_descr_t fifo_w_data_in, fifo_w_data_out;

    /* AW QUEUE */
    fifo_v3 #(
        .dtype     (ax_descr_t),
        .DEPTH     (AW_FIFO_DEPTH)
    ) i_aw_fifo (
        .clk_i     (clk_i),
        .rst_ni    (rst_ni),
        .flush_i   (1'b0),
        .testmode_i(1'b0),
        .full_o    (fifo_aw_full),
        .empty_o   (fifo_aw_empty),
        .usage_o   (),
        .data_i    (fifo_ax_data_in),
        .push_i    (fifo_aw_push),
        .data_o    (fifo_aw_data_out),
        .pop_i     (fifo_aw_pop)
    );

    /* AR QUEUE */
    fifo_v3 #(
        .dtype     (ax_descr_t),
        .DEPTH     (AR_FIFO_DEPTH)
    ) i_ar_fifo (
        .clk_i     (clk_i),
        .rst_ni    (rst_ni),
        .flush_i   (1'b0),
        .testmode_i(1'b0),
        .full_o    (fifo_ar_full),
        .empty_o   (fifo_ar_empty),
        .usage_o   (),
        .data_i    (fifo_ax_data_in),
        .push_i    (fifo_ar_push),
        .data_o    (fifo_ar_data_out),
        .pop_i     (fifo_ar_pop)
    );

    /* W QUEUE */
    fifo_v3 #(
        .dtype     (w_descr_t),
        .DEPTH     (W_FIFO_DEPTH)
    ) i_w_fifo (
        .clk_i     (clk_i),
        .rst_ni    (rst_ni),
        .flush_i   (1'b0),
        .testmode_i(1'b0),
        .full_o    (fifo_w_full),
        .empty_o   (fifo_w_empty),
        .usage_o   (),
        .data_i    (fifo_w_data_in),
        .push_i    (fifo_w_push),
        .data_o    (fifo_w_data_out),
        .pop_i     (fifo_w_pop)
    );
    
    /* WRITE IDs QUEUE */
    fifo_v3 #(
        .dtype     (cmd_id_t),
        .DEPTH     (WRITES_FIFO_DEPTH)
    ) i_write_id_fifo (
        .clk_i     (clk_i),
        .rst_ni    (rst_ni),
        .flush_i   (1'b0),
        .testmode_i(1'b0),
        .full_o    (fifo_write_id_full),
        .empty_o   (fifo_write_id_empty),
        .usage_o   (),
        .data_i    (cmd_req_i.cmd_id),
        .push_i    (fifo_write_id_push),
        .data_o    (fifo_write_id_out),
        .pop_i     (fifo_write_id_pop)
    );
    
    /* READ IDs QUEUE */
    fifo_v3 #(
        .dtype     (cmd_id_t),
        .DEPTH     (READS_FIFO_DEPTH)
    ) i_read_id_fifo (
        .clk_i     (clk_i),
        .rst_ni    (rst_ni),
        .flush_i   (1'b0),
        .testmode_i(1'b0),
        .full_o    (fifo_read_id_full),
        .empty_o   (fifo_read_id_empty),
        .usage_o   (),
        .data_i    (cmd_req_i.cmd_id),
        .push_i    (fifo_read_id_push),
        .data_o    (fifo_read_id_out),
        .pop_i     (fifo_read_id_pop)
    );
    
    // We are ready to accept commands only if we can push to the queues
    assign cmd_req_ready_o = (cmd_req_i.descr.host_direct_cmd.nic_to_host == 1'b1 && !fifo_aw_full && !fifo_w_full && !fifo_write_id_full) || (cmd_req_i.descr.host_direct_cmd.nic_to_host == 1'b0 && !fifo_ar_full && !fifo_read_id_full);

    // Define push logic
    assign fifo_aw_push = cmd_req_valid_i && cmd_req_ready_o && cmd_req_i.descr.host_direct_cmd.nic_to_host == 1'b1;
    assign fifo_w_push = fifo_aw_push;
    assign fifo_ar_push = cmd_req_valid_i && cmd_req_ready_o && cmd_req_i.descr.host_direct_cmd.nic_to_host == 1'b0;
    assign fifo_write_id_push = fifo_aw_push;
    assign fifo_read_id_push = fifo_ar_push;    

    // Define pop logic
    assign fifo_aw_pop = host_resp_i.aw_ready && host_req_o.aw_valid; 
    assign fifo_ar_pop = host_resp_i.ar_ready && host_req_o.ar_valid;
    assign fifo_w_pop  = host_resp_i.w_ready && host_req_o.w_valid;
    assign fifo_write_id_pop = host_req_o.b_ready && host_resp_i.b_valid;
    assign fifo_read_id_pop = host_req_o.r_ready && host_resp_i.r_valid;

    // Define new AX to push
    assign fifo_ax_data_in.address = cmd_req_i.descr.host_direct_cmd.host_addr;

    // Define new W to push
    assign fifo_w_data_in.data[CMD_IMM_DATA_SIZE-1:0] = cmd_req_i.descr.host_direct_cmd.imm_data[CMD_IMM_DATA_SIZE-1:0];
    assign fifo_w_data_in.strb    = '1 >> (AXI_STRB - cmd_req_i.descr.host_direct_cmd.imm_data_size);

    // Define valid outputs
    assign host_req_o.aw_valid = ~fifo_aw_empty;
    assign host_req_o.ar_valid = ~fifo_ar_empty;
    assign host_req_o.w_valid = ~fifo_w_empty;

    // Define AW output
    assign host_req_o.aw.id     = BaseHDId;
    assign host_req_o.aw.addr   = fifo_aw_data_out.address;
    assign host_req_o.aw.len    = 8'h00;
    assign host_req_o.aw.size   = 3'b110;
    assign host_req_o.aw.burst  = axi_pkg::BURST_INCR;
    assign host_req_o.aw.lock   = 1'b0;
    assign host_req_o.aw.cache  = 4'h0;
    assign host_req_o.aw.prot   = 3'b000;
    assign host_req_o.aw.qos    = 4'h0;
    assign host_req_o.aw.region = 4'h0;
    assign host_req_o.aw.atop   = 6'b000000;
    assign host_req_o.aw.user   = '0;

    // Define AR output
    assign host_req_o.ar.id     = BaseHDId;
    assign host_req_o.ar.addr   = fifo_ar_data_out.address;
    assign host_req_o.ar.len    = 8'h00;
    assign host_req_o.ar.size   = 3'b110;
    assign host_req_o.ar.burst  = axi_pkg::BURST_INCR;
    assign host_req_o.ar.lock   = 1'b0;
    assign host_req_o.ar.cache  = 4'h0;
    assign host_req_o.ar.prot   = 3'b000;
    assign host_req_o.ar.qos    = 4'h0;
    assign host_req_o.ar.region = 4'h0;
    assign host_req_o.ar.user   = '0;

    // Define W output
    assign host_req_o.w.data    = fifo_w_data_out.data;
    assign host_req_o.w.strb    = fifo_w_data_out.strb;
    assign host_req_o.w.last    = 1'b1;
    assign host_req_o.w.user    = '0;

    // Handle AXI responses
    always_comb begin
        cmd_resp_o.cmd_id = '0;
        cmd_resp_valid_o = 1'b0;
        host_req_o.r_ready = 1'b0;
        host_req_o.b_ready = 1'b0;

        if (host_resp_i.r_valid) begin
            host_req_o.r_ready = 1'b1;
            cmd_resp_o.cmd_id = fifo_read_id_out;
            cmd_resp_valid_o = 1'b1;
        end 
        else if (host_resp_i.b_valid ) begin
            host_req_o.b_ready = 1'b1;
            cmd_resp_o.cmd_id = fifo_write_id_out;
            cmd_resp_valid_o = 1'b1;
        end
    end

    // Assertions
    assert property(
      @(posedge clk_i) (CMD_IMM_DATA_SIZE <= AXI_DW))
        else $fatal (1, "Command immediate data cannot be bigger than AXI data channel width!");
    


endmodule
