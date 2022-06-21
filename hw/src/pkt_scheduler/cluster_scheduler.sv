// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

import pspin_cfg_pkg::*;

module cluster_scheduler #(
    parameter int NUM_HERS_PER_CLUSTER  = 64,
    parameter int L1_PKT_BUFF_SIZE      = 512,
    parameter int L1_CLUSTER_BASE       = 0,
    parameter int L1_CLUSTER_MEM_SIZE   = 0,
    parameter int L1_RUNTIME_OFFSET     = 0,
    parameter int TASKS_FIFO_DEPTH      = 1
) (

    input logic                                         clk_i,
    input logic                                         rst_ni,

    input logic [5:0]                                   cluster_id_i,

    //task from scheduler
    input  logic                                        task_valid_i,
    output logic                                        task_ready_o,
    input  handler_task_t                               task_descr_i,

    //feedback to scheduler
    output logic                                        feedback_valid_o,
    input  logic                                        feedback_ready_i,
    output feedback_descr_t                             feedback_o,

    //dma request to DMA engine
    output logic                                        dma_xfer_valid_o,
    input  logic                                        dma_xfer_ready_i,
    output transf_descr_32_t                            dma_xfer_o,

    //dma response from DMA engine
    input  logic                                        dma_resp_i,

    //task_descr_t to HPU
    output logic [NUM_CORES-1:0]                        hpu_task_valid_o,
    input  logic [NUM_CORES-1:0]                        hpu_task_ready_i,
    output hpu_handler_task_t                           hpu_task_o,

    //feedback from HPUs
    input  logic [NUM_CORES-1:0]                        hpu_feedback_valid_i,
    output logic [NUM_CORES-1:0]                        hpu_feedback_ready_o,
    input  task_feedback_descr_t [NUM_CORES-1:0]        hpu_feedback_i,

    //activation signal from HPUs
    input  logic [NUM_CORES-1:0]                        hpu_active_i,

    //activation signal out
    output logic                                        cluster_active_o
);

    localparam int unsigned PktBuffMemSlotSize = 64;
    localparam int unsigned NumRB = 4;
    typedef logic [$clog2(L1_PKT_BUFF_SIZE):0]   pkt_buf_size_t;
    typedef logic [$clog2(L1_PKT_BUFF_SIZE)-1:0] pkt_buf_idx_t;

    logic [$clog2(NUM_HERS_PER_CLUSTER):0] to_pop_d;
    logic [$clog2(NUM_HERS_PER_CLUSTER):0] to_pop_q;

    //tasks which DMA xfers are still in-flight
    logic        dma_req_empty;
    logic        dma_req_full;
    //set if a request has been popped (i.e., dma resp recvd + assigned to core)
    logic        dma_req_pop, dma_req_pop_nz;
    hpu_handler_task_t ready_task;
    hpu_handler_task_t new_task;

    //true if we can issue a DMA transfer a
    logic can_issue_dma;

    logic [31:0] l1_pkt_base_addr;
    logic [31:0] l1_pkt_ptr;

    //free HPUs
    logic [$clog2(NUM_CORES)-1:0]   free_hpu_idx;
    logic                           no_free_hpu;

    //L1 packet buffer
    pkt_buf_idx_t                   free_pkt_idx;
    pkt_buf_idx_t                   feedback_pkt_idx;
    pkt_buf_size_t                  pkt_buff_free_space;

    //true if the HER allocator is ready
    logic pkt_alloc_ready; //unused in synthesis

    //internal state
    typedef enum logic {Ready, WaitDMA} state_t;
    state_t state_d, state_q;

    transf_descr_32_t dma_xfer, dma_xfer_q, dma_xfer_d;

    // buffer the tasks in a fifo
    fifo_v3 #(
        .dtype     (hpu_handler_task_t),
        .DEPTH     (NUM_HERS_PER_CLUSTER)
    ) i_dma_request_fifo (
        .clk_i     (clk_i),
        .rst_ni    (rst_ni),
        .flush_i   (1'b0),
        .testmode_i(1'b0),
        .full_o    (dma_req_full),
        .empty_o   (dma_req_empty),
        .usage_o   (),
        .data_i    (new_task),
        .push_i    (task_valid_i && task_ready_o),
        .data_o    (ready_task),
        .pop_i     (dma_req_pop)
    );

    //idle HPUs
    lzc #(
        .WIDTH  (NUM_CORES)
    ) i_lzc_free_hpus (
        .in_i    (hpu_task_ready_i),
        .cnt_o   (free_hpu_idx),
        .empty_o (no_free_hpu)
    );

    // Packet buffer allocator
    cluster_rb_shim #(
        .BuffMemLength  (L1_PKT_BUFF_SIZE),
        .MemSlotSize    (PktBuffMemSlotSize),
        .NumRB          (NumRB)
    ) i_her_alloc (
        .clk_i          (clk_i),
        .rst_ni         (rst_ni),

        .alloc_valid_i  (task_valid_i && task_ready_o),
        .alloc_ready_o  (pkt_alloc_ready),
        .alloc_size_i   (task_descr_i.pkt_size[$clog2(L1_PKT_BUFF_SIZE):0]),
        .alloc_index_o  (free_pkt_idx),

        .free_valid_i   (feedback_valid_o && feedback_ready_i),
        .free_index_i   (feedback_pkt_idx),
        .free_size_i    (hpu_feedback_arb_i.feedback_descr.pkt_size[$clog2(L1_PKT_BUFF_SIZE):0]),

        .free_space_o   (pkt_buff_free_space)
    );

    // HPU feedbacks to cluster feedback arbiter
    task_feedback_descr_t hpu_feedback_arb_i;
    rr_arb_tree #(
        .NumIn      (NUM_CORES),
        .DataType   (task_feedback_descr_t),
        .ExtPrio    (0),
        .AxiVldRdy  (1),
        .LockIn     (1)
    ) i_hpu_feedback_rr_arb (
        .clk_i      (clk_i),
        .rst_ni     (rst_ni),
        .flush_i    (1'b0),
        .rr_i       ('0),
        .req_i      (hpu_feedback_valid_i),
        .gnt_o      (hpu_feedback_ready_o),
        .data_i     (hpu_feedback_i),
        .gnt_i      (feedback_ready_i),
        .req_o      (feedback_valid_o),
        .data_o     (hpu_feedback_arb_i),
        .idx_o      ()
    );

    assign cluster_active_o = (~hpu_active_i == '0);

    assign l1_pkt_base_addr = (L1_CLUSTER_BASE + cluster_id_i * L1_CLUSTER_MEM_SIZE) + L1_PKT_BUFF_OFFSET;
    assign l1_pkt_ptr       = l1_pkt_base_addr + free_pkt_idx;
    assign feedback_pkt_idx = hpu_feedback_arb_i.pkt_ptr - l1_pkt_base_addr;

    /*** Accepting tasks and starting DMA xfers ***/

    //define a new task
    assign new_task.handler_task = task_descr_i;
    assign new_task.pkt_ptr      = l1_pkt_ptr;

    //define DMA xfer
    assign can_issue_dma = task_valid_i && task_ready_o && task_descr_i.pkt_size != '0;

    assign dma_xfer.num_bytes     = task_descr_i.pkt_size;
    assign dma_xfer.src_addr      = task_descr_i.pkt_addr;
    assign dma_xfer.dst_addr      = l1_pkt_ptr;

    assign dma_xfer.decouple      = 1'b1;
    assign dma_xfer.deburst       = 1'b0;
    assign dma_xfer.serialize     = 1'b0; // TODO: connect me!

    assign dma_xfer_d = (state_q == Ready) ? dma_xfer : dma_xfer_q;
    assign dma_xfer_o = (state_q == Ready) ? dma_xfer : dma_xfer_q;
    assign dma_xfer_valid_o = (state_q == Ready && can_issue_dma) || (state_q == WaitDMA);

    //we are ready to accept new tasks if
    //  - we are in Ready state AND
    //  - we can buffer the new DMA xfer AND
    //  - we have an HER in L1 where we can copy the L2 HER
    //This is a bit redundant because we expect the scheduler to not forward
    //us tasks if we are at capacity.
    assign task_ready_o = (state_q == Ready) && (!dma_req_full) && (pkt_buff_free_space >= task_descr_i.pkt_size);

    always_comb begin
        state_d = state_q;

        case (state_q)
            Ready: begin
                //we don't issue a DMA transfer for zero-byte task (e.g., header, completion)
                if (can_issue_dma) begin
                    state_d = (dma_xfer_ready_i) ? Ready : WaitDMA;
                end
            end

            WaitDMA: begin
                if (dma_xfer_ready_i) begin
                    state_d = Ready;
                end
            end
        endcase
    end

    /*** Other side of the FIFO: popping and assigning to free HPUs ***/

    //we pop if there is a free HPU and if there is a completed xfer
    assign dma_req_pop    = !dma_req_empty && !no_free_hpu && (to_pop_q > 0 || ready_task.handler_task.pkt_size == 0);

    //this gets asserted if we are popping an entry associated with an actual DMA transfer.
    assign dma_req_pop_nz = !dma_req_empty && !no_free_hpu && to_pop_q > 0 && ready_task.handler_task.pkt_size > 0;

    //ready hput tasks goes to all HPUs' outputs but only one will be enabled
    assign hpu_task_o = ready_task;
    for (genvar i = 0; i < NUM_CORES; i++) begin : gen_hpu_task
        assign hpu_task_valid_o[i] = dma_req_pop & (i == free_hpu_idx);
    end

    /*** Feedback forwarding ***/
    assign feedback_o = hpu_feedback_arb_i.feedback_descr;


    /*** Internal state ***/

    //count how many DMA xfers can be popped.
    //+1 if we get a DMA completion but do not pop at this cycle (e.g., no free HPU)
    //-1 if we can pop at this cycle but did not get a DMA completion
    //+0 if we get a DMA completion and also pop in this cycle
    always_comb begin
        case ({dma_resp_i, dma_req_pop_nz})
            2'b10   : to_pop_d = to_pop_q + 1;
            2'b01   : to_pop_d = to_pop_q - 1;
            default : to_pop_d = to_pop_q;
        endcase
    end

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
            to_pop_q <= '0;
            state_q <= Ready;
            dma_xfer_q <= '0;
        end else begin
            to_pop_q <= to_pop_d;
            state_q <= state_d;
            dma_xfer_q <= dma_xfer_d;
        end
    end

    `ifndef VERILATOR
    // pragma translate_off
    initial begin
        forever begin
            @(posedge clk_i);
            if (task_valid_i && task_ready_o) begin
                $display("%0d CLUSTER %0d got task (msg_id: %0d; size: %0d; addr: %0d)!", $time, cluster_id_i, task_descr_i.msgid, task_descr_i.pkt_size, task_descr_i.pkt_addr);

                if (dma_xfer_valid_o && dma_xfer_ready_i && dma_xfer.src_addr[5:0] != '0) begin
                    $display("WARNING: source address of DMA transfer is not 512-bit aligned: this will negatively impact performance!");
                end
                if (dma_xfer_valid_o && dma_xfer_ready_i && dma_xfer.dst_addr[5:0] != '0) begin
                    $display("WARNING: destination address of DMA transfer is not 512-bit aligned: this will negatively impact performance!");
                end
            end
        end
    end

    initial begin : p_assertions

        assert property (@(posedge clk_i) (dma_req_pop) |-> (!dma_req_empty)) else
            $fatal(1, "We cannot pop from an empty queue!");

        assert property (@(posedge clk_i) (task_valid_i && task_ready_o) |-> (pkt_buff_free_space >= task_descr_i.pkt_size)) else
            $fatal(1, "We received a packet that cannot store!");

    end
    // pragma translate_on
    `endif

endmodule