// Copyright (c) 2021 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module hpu_driver #(
    parameter int unsigned NUM_CLUSTERS          = 4,
    parameter int unsigned NUM_CMDS              = 4,
    parameter int unsigned CLUSTER_ID_WIDTH      = 16,
    parameter int unsigned CORE_ID_WIDTH         = 16,
    parameter int unsigned DATA_WIDTH            = 32,
    parameter type         dreq_t                = logic,
    parameter type         drsp_t                = logic,
    parameter type         drsp_chan_t           = logic,
    parameter type         hpu_handler_task_t    = logic,
    parameter type         task_feedback_descr_t = logic,
    parameter type         cmd_req_t             = logic,
    parameter type         cmd_resp_t            = logic
) (
    input  logic                  clk_i,
    input  logic                  rst_ni,

    input  logic [31:0]           hart_id_i,

    //task in
    input  logic                  hpu_task_valid_i,
    output logic                  hpu_task_ready_o, 
    input  hpu_handler_task_t     hpu_task_i,

    //feedback out
    output logic                  hpu_feedback_valid_o,
    input  logic                  hpu_feedback_ready_i,
    output task_feedback_descr_t  hpu_feedback_o,

    //high if we are ready to accept tasks
    output logic                  hpu_active_o,

    //core interface
    input  dreq_t                 core_req_i,
    output drsp_t                 core_resp_o,

    //high if this core has no pending DMA requests
    input logic                   no_dma_req_pending_i,

    //command out
    input  logic                  cmd_ready_i,
    output logic                  cmd_valid_o,
    output cmd_req_t              cmd_o,

    //command completion notification in
    input  logic                  cmd_resp_valid_i,
    input  cmd_resp_t             cmd_resp_i
);
    localparam int unsigned SelBitOffset = 7;

    logic no_pending_cmd;

    logic frontend_select_q, frontend_select_d;

    dreq_t task_frontend_req, cmd_frontend_req;
    drsp_t task_frontend_resp, cmd_frontend_resp;

    logic [CLUSTER_ID_WIDTH-1:0] cluster_id;
    logic [CORE_ID_WIDTH-1:0]    core_id;

    logic can_send_feedback;
    logic cmd_resp_valid;
    logic disable_commands;
    logic handler_terminated;

    assign frontend_select_d = (core_req_i.q_valid) ? core_req_i.q.addr[SelBitOffset] : frontend_select_q;

    assign cluster_id = hart_id_i[31:CLUSTER_ID_WIDTH];
    assign core_id = hart_id_i[CLUSTER_ID_WIDTH-1:0];

    assign can_send_feedback = no_pending_cmd;
    assign cmd_resp_valid = cmd_resp_valid_i && cmd_resp_i.cmd_id.cluster_id == cluster_id && cmd_resp_i.cmd_id.core_id == core_id;

    stream_demux #(
        .N_OUP(2)
    ) i_frontend_demux (
        .inp_valid_i    ( core_req_i.q_valid                                      ),
        .inp_ready_o    ( core_resp_o.q_ready                                     ),
        .oup_sel_i      ( frontend_select_d                                       ),
        .oup_valid_o    ( {cmd_frontend_req.q_valid,  task_frontend_req.q_valid  }),
        .oup_ready_i    ( {cmd_frontend_resp.q_ready, task_frontend_resp.q_ready })
    );

    assign task_frontend_req.q = core_req_i.q;
    assign cmd_frontend_req.q = core_req_i.q;

    stream_mux #(
        .DATA_T(drsp_chan_t),
        .N_INP(2)
    ) i_frontend_mux (
        .inp_data_i   ( {cmd_frontend_resp.p,       task_frontend_resp.p       }),
        .inp_valid_i  ( {cmd_frontend_resp.p_valid, task_frontend_resp.p_valid }),
        .inp_ready_o  ( {cmd_frontend_req.p_ready,  task_frontend_req.p_ready  }),
        .inp_sel_i    ( frontend_select_q                                       ),
        .oup_data_o   ( core_resp_o.p                                           ),
        .oup_valid_o  ( core_resp_o.p_valid                                     ),
        .oup_ready_i  ( core_req_i.p_ready                                      )
    );    

    task_frontend #(
        .NUM_CLUSTERS              (NUM_CLUSTERS),
        .CLUSTER_ID_WIDTH          (CLUSTER_ID_WIDTH),
        .CORE_ID_WIDTH             (CORE_ID_WIDTH),
        .DATA_WIDTH                (DATA_WIDTH),
        .hpu_handler_task_t        (hpu_handler_task_t),
        .task_feedback_descr_t     (task_feedback_descr_t),
        .dreq_t                    (dreq_t),
        .drsp_t                    (drsp_t),
        .drsp_chan_t               (drsp_chan_t)
    ) i_task_frontend (
        .clk_i                     (clk_i),
        .rst_ni                    (rst_ni),
        .cluster_id_i              (cluster_id),
        .core_id_i                 (core_id),
        .hpu_task_valid_i          (hpu_task_valid_i),
        .hpu_task_ready_o          (hpu_task_ready_o),
        .hpu_task_i                (hpu_task_i),
        .hpu_feedback_valid_o      (hpu_feedback_valid_o),
        .hpu_feedback_ready_i      (hpu_feedback_ready_i),
        .hpu_feedback_o            (hpu_feedback_o),
        .hpu_active_o              (hpu_active_o),
        .core_req_i                (task_frontend_req),
        .core_resp_o               (task_frontend_resp),
        .can_send_feedback_i       (can_send_feedback),
        .disable_commands_o        (disable_commands),
        .handler_terminated_o      (handler_terminated)
    );

    cmd_frontend #(
        .NUM_CMDS                  (NUM_CMDS),
        .NUM_BUFFERED_CMD          (NUM_CMDS),
        .CLUSTER_ID_WIDTH          (CLUSTER_ID_WIDTH),
        .CORE_ID_WIDTH             (CORE_ID_WIDTH),
        .DATA_WIDTH                (DATA_WIDTH),
        .cmd_req_t                 (cmd_req_t),
        .cmd_resp_t                (cmd_resp_t),
        .dreq_t                    (dreq_t),
        .drsp_t                    (drsp_t),
        .drsp_chan_t               (drsp_chan_t)
    ) i_cmd_frontend (
        .clk_i                     (clk_i),
        .rst_ni                    (rst_ni),
        .cluster_id_i              (cluster_id),
        .core_id_i                 (core_id),
        .core_req_i                (cmd_frontend_req),
        .core_resp_o               (cmd_frontend_resp),
        .cmd_resp_valid_i          (cmd_resp_valid),
        .cmd_resp_i                (cmd_resp_i),
        .disable_commands_i        (disable_commands),
        .release_all_commands_i    (handler_terminated),
        .no_pending_cmd_o          (no_pending_cmd),
        .cmd_ready_i               (cmd_ready_i),
        .cmd_valid_o               (cmd_valid_o),
        .cmd_o                     (cmd_o)
    );

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
            frontend_select_q <= 0; 
        end else begin
            frontend_select_q <= frontend_select_d;
        end
    end

endmodule
