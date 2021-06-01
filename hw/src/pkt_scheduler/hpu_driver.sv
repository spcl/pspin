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
    parameter int unsigned  NUM_CLUSTERS          = 4,
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

    assign frontend_select_d = (core_req_i.q_valid) ? core_req_i.q.addr[SelBitOffset] : frontend_select_q;

    assign cluster_id = hart_id_i[31:CLUSTER_ID_WIDTH];
    assign core_id = hart_id_i[CLUSTER_ID_WIDTH-1:0];

    assign can_send_feedback = 1'b1; /* FIX ME no_dma_req_pending_i && no_pending_cmd; */
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
        .inp_data_i     ( {cmd_frontend_resp.p,       task_frontend_resp.p       }),
        .inp_valid_i    ( {cmd_frontend_resp.p_valid, task_frontend_resp.p_valid }),
        .inp_ready_o    ( {cmd_frontend_req.p_ready,  task_frontend_req.p_ready  }),
        .inp_sel_i      ( frontend_select_q                                       ),
        .oup_data_o     ( core_resp_o.p                                           ),
        .oup_valid_o    ( core_resp_o.p_valid                                     ),
        .oup_ready_i    ( core_req_i.p_ready                                      )
    );    

    task_frontend #(
        .NUM_CLUSTERS              (NUM_CLUSTERS),
        .CLUSTER_ID_WIDTH          (CLUSTER_ID_WIDTH),
        .CORE_ID_WIDTH             (CORE_ID_WIDTH),
        .DATA_WIDTH                (DATA_WIDTH),
        .hpu_handler_task_t        (hpu_handler_task_t),
        .task_feedback_descr_t     (task_feedback_descr_t),
        .dreq_t                    (dreq_t),
        .drsp_t                    (drsp_t)
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
        .disable_commands_o        (disable_commands)
    );

    cmd_frontend #(
        .NUM_CMDS                  (NUM_CMDS),
        .NUM_BUFFERED_CMD          (NUM_CMDS),
        .cmd_req_t                 (cmd_req_t),
        .cmd_resp_t                (cmd_resp_t),
        .dreq_t                    (dreq_t),
        .drsp_t                    (drsp_t)
    ) i_cmd_frontend (
        .clk_i                     (clk_i),
        .rst_ni                    (rst_ni),
        .cluster_id_i              (cluster_id),
        .core_id_i                 (core_id),
        .core_req_i                (cmd_frontend_req),
        .core_resp_o               (cmd_frontend_resp),
        .cmd_resp_valid_i          (cmd_resp_valid),
        .cmd_resp_i                (cmd_resp_i),
        .disabled_i                (disable_commands),
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


module task_frontend #(
    parameter int unsigned NUM_CLUSTERS        = 4,
    parameter int unsigned CLUSTER_ID_WIDTH    = 16,
    parameter int unsigned CORE_ID_WIDTH       = 16,
    parameter int unsigned DATA_WIDTH          = 32,
    parameter type hpu_handler_task_t          = logic,
    parameter type task_feedback_descr_t       = logic,
    parameter type  dreq_t                     = logic,
    parameter type  drsp_t                     = logic
) (
    input logic                        clk_i,
    input logic                        rst_ni,

    input logic [CLUSTER_ID_WIDTH-1:0] cluster_id_i,
    input logic [CORE_ID_WIDTH-1:0]    core_id_i,

    //task in
    input  logic                       hpu_task_valid_i,
    output logic                       hpu_task_ready_o, 
    input  hpu_handler_task_t          hpu_task_i,

    //feedback out
    output logic                       hpu_feedback_valid_o,
    input  logic                       hpu_feedback_ready_i,
    output task_feedback_descr_t       hpu_feedback_o,

    output logic                       hpu_active_o,

    input  dreq_t                      core_req_i,
    output drsp_t                      core_resp_o,

    output logic                       disable_commands_o,
    input  logic                       can_send_feedback_i
);

    localparam int unsigned DataAlign = $clog2(DATA_WIDTH/8);

    typedef enum logic [2:0] {Init, Idle, Running, StallingFeedback, StallingResponse} state_t;
    state_t state_d, state_q;
    logic [DataAlign-1:0] offset_d, offset_q;

    hpu_handler_task_t current_task_q, current_task_d;

    logic trigger_feedback_d, trigger_feedback_q;

    logic valid_d, valid_q;
    logic [31:0] rdata_d, rdata_q;

    logic [$clog2(NUM_CLUSTERS)-1:0] home_cluster_id;

    logic [31:0] l1_home_base_addr;
    logic [31:0] l1_pkt_addr;

    logic [31:0] handler_error_code;
    logic handler_error;

    logic response_blocked, feedback_blocked;

    //buffer feedback waiting for command to complete
    //NOTE: only one feedback at time can be buffered with this implementation!
    task_feedback_descr_t hpu_feedback;
    logic feedback_buff_not_full, feedback_buff_full;
    logic feedback_buff_push;

    stream_fifo #(
        .FALL_THROUGH (1'b0),
        .DEPTH (1),
        .T(task_feedback_descr_t)
    ) i_feedback_buff (
        .clk_i          (clk_i),
        .rst_ni         (rst_ni),
        .flush_i        (1'b0),
        .testmode_i     (1'b0),
        .usage_o        (),
        .data_i         (hpu_feedback),
        .valid_i        (feedback_buff_push),
        .ready_o        (feedback_buff_not_full),
        .data_o         (hpu_feedback_o),  
        .valid_o        (hpu_feedback_valid_o), 
        .ready_i        (hpu_feedback_ready_i) 
    );

    assign feedback_buff_full = ~feedback_buff_not_full;
    assign feedback_buff_push = trigger_feedback_d || (state_q == StallingFeedback);

    assign disable_commands_o = hpu_feedback_valid_o;

    assign core_resp_o.p.data = rdata_q << {offset_q, 3'b000};
    assign core_resp_o.p_valid = valid_q;
    assign core_resp_o.p.error = 1'b0; /* FIX ME */

    assign home_cluster_id = current_task_q.handler_task.msgid[$clog2(NUM_CLUSTERS)-1:0];
    assign l1_pkt_addr = current_task_q.pkt_ptr;

    //building feedback
    assign hpu_feedback.pkt_ptr                         = current_task_q.pkt_ptr;
    assign hpu_feedback.feedback_descr.pkt_addr         = current_task_q.handler_task.pkt_addr;
    assign hpu_feedback.feedback_descr.msgid            = current_task_q.handler_task.msgid;
    assign hpu_feedback.feedback_descr.pkt_size         = current_task_q.handler_task.pkt_size;
    assign hpu_feedback.feedback_descr.trigger_feedback = current_task_q.handler_task.trigger_feedback;

    assign hpu_task_ready_o = (state_q == Idle);

    assign hpu_active_o = state_q != Init;

    assign response_blocked = (core_resp_o.p_valid && ~core_req_i.p_ready);
    assign feedback_blocked = (trigger_feedback_d && feedback_buff_full);

    always_comb begin
        state_d = state_q;
        current_task_d = current_task_q;

        case (state_q)
            Init: begin
                if (core_req_i.q_valid) begin
                    state_d = Idle;
                end
            end

            Idle: begin
                if (hpu_task_valid_i) begin
                    state_d = (hpu_task_i.handler_task.handler_fun == '0) ? StallingFeedback : Running;
                    current_task_d = hpu_task_i;
                end
            end 

            Running: begin 
                if (response_blocked) begin
                    state_d = StallingResponse;
                end 
                else if (feedback_blocked) begin
                    state_d = StallingFeedback;
                end 
                else if (trigger_feedback_d) begin
                    state_d = Idle;
                end
            end

            StallingResponse: begin
                if (!response_blocked) begin
                    state_d = (feedback_blocked) ? StallingFeedback : Running;
                end
            end

            StallingFeedback: begin
                if (!feedback_buff_full) begin
                    state_d = Idle;
                end
            end

            default: begin 
                state_d = Idle;
            end
        endcase
    end
        
    always_comb begin   
        core_resp_o.q_ready = 1'b0;
        rdata_d = rdata_q;
        valid_d = (state_q != StallingResponse) ? 1'b0 : valid_q;
        handler_error_code = '0;
        handler_error = 1'b0;
        offset_d = offset_q;

        trigger_feedback_d = ((state_q == Running && core_req_i.q_valid) || state_q == Idle) ? 1'b0 : trigger_feedback_q;

        if (state_q == Running && core_req_i.q_valid) begin
            core_resp_o.q_ready = 1'b1;
            valid_d = 1'b1;
            offset_d = core_req_i.q.addr[DataAlign-1:0];

            case (core_req_i.q.addr[7:0]) 

                /* Task info */
                8'h00: begin //handler function
                    rdata_d = current_task_q.handler_task.handler_fun; 
                end
                8'h04: begin //handler function size (not needed?)
                    rdata_d = current_task_q.handler_task.handler_fun_size;
                end
                8'h08: begin //handler memory address (L2)
                    rdata_d = current_task_q.handler_task.handler_mem_addr;
                end
                8'h0c: begin //handler memory size 
                    rdata_d = current_task_q.handler_task.handler_mem_size;
                end
                8'h10: begin  //L1 packet address
                    rdata_d = l1_pkt_addr;
                end
                8'h14: begin //packet size
                    rdata_d = current_task_q.handler_task.pkt_size;
                end
                8'h18: begin //scratchpad address 0
                    rdata_d = current_task_q.handler_task.scratchpad_addr[0];
                end
                8'h1c: begin //scratchpad address 1
                    rdata_d = current_task_q.handler_task.scratchpad_addr[1];
                end
                8'h20: begin //scratchpad address 2
                    rdata_d = current_task_q.handler_task.scratchpad_addr[2];
                end
                8'h24: begin //scratchpad address 3
                    rdata_d = current_task_q.handler_task.scratchpad_addr[3];
                end                
                8'h28: begin //scratchpad size 0
                    rdata_d = current_task_q.handler_task.scratchpad_size[0];
                end
                8'h2c: begin //scratchpad size 1
                    rdata_d = current_task_q.handler_task.scratchpad_size[1];
                end
                8'h30: begin //scratchpad size 2
                    rdata_d = current_task_q.handler_task.scratchpad_size[2];
                end
                8'h34: begin //scratchpad size 3
                    rdata_d = current_task_q.handler_task.scratchpad_size[3];
                end
                8'h38: begin //host memory address (high)
                    rdata_d = current_task_q.handler_task.host_mem_addr[63:32];
                end
                8'h3c: begin //host memory address (low)
                    rdata_d = current_task_q.handler_task.host_mem_addr[31:0];
                end
                8'h40: begin //host memory size
                    rdata_d = current_task_q.handler_task.host_mem_size;
                end
                8'h44: begin //L2 packet address
                    rdata_d = current_task_q.handler_task.pkt_addr;
                end
                8'h48: begin //home cluster ID
                    rdata_d = home_cluster_id;
                end
                8'h4c: begin //Message ID
                    rdata_d = current_task_q.handler_task.msgid;
                end

                /* Handler termination */
                8'h50: begin //feedback flag (reading this address leads to the sending of the feedback)
                    rdata_d = 32'h00000000;
                    trigger_feedback_d = 1'b1;
                end

                /* Handler error */
                8'h54: begin
                    if (core_req_i.q.write) begin
                        handler_error_code = core_req_i.q.data;
                        handler_error = 1'b1;
                    end
                end
            endcase
        end
    end
    
    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
            state_q <= Init; 
            current_task_q <= '0; //how to initialize this?
            valid_q <= 1'b0;
            rdata_q <= '0;
            trigger_feedback_q <= 1'b0;
            offset_q <= '0;
        end else begin
            state_q <= state_d;
            current_task_q <= current_task_d;
            valid_q <= valid_d;
            rdata_q <= rdata_d;
            trigger_feedback_q <= trigger_feedback_d;
            offset_q <= offset_d;
        end
    end
    
    // pragma translate_off
    `ifndef VERILATOR
    initial begin
        static int handler_start_time = 0;
        static int timediff;

        forever begin            
            @(posedge clk_i);
            if (hpu_task_valid_i && hpu_task_ready_o) begin
                handler_start_time = $stime;
                $display("%0d INFO HANDLER_START %0d %0d", $stime, cluster_id_i, core_id_i);
            end

            if (state_q != Init && state_q != Idle && state_d == Idle) begin
                timediff = $stime - handler_start_time;
                $display("%0d INFO HPU_TIME %0d %0d %0d", $stime, cluster_id_i, core_id_i, timediff);                  
            end

            if (state_q == Running && trigger_feedback_d) begin
                timediff = $stime - handler_start_time;
                $display("%0d INFO HANDLER_TIME %0d %0d %0d %0d %0d %0d %0d", $stime, cluster_id_i, core_id_i, current_task_q.handler_task.msgid, current_task_q.handler_task.handler_fun, timediff, current_task_q.handler_task.pkt_addr, current_task_q.handler_task.pkt_size);
            end

            if (handler_error) begin
                $display("%0d HPU (%0d %0d) HANDLER ERROR: %0d", $stime, cluster_id_i, core_id_i, handler_error_code);
            end
        end
    end
    `else
        always_ff @(posedge clk_i, negedge rst_ni) begin
            if (hpu_task_valid_i && hpu_task_ready_o) begin
                $display("[%0d][synt]: INFO HANDLER_START %0d %0d", $stime, cluster_id_i, core_id_i);
            end

            if (state_q != Init && state_q != Idle && state_d == Idle) begin
                $display("[%0d][synt]: INFO HPU_TIME %0d %0d", $stime, cluster_id_i, core_id_i);                  
            end

            if (state_q == Running && trigger_feedback_d == 1'b1 && trigger_feedback_q == 1'b0) begin
                $display("[%0d][synt]: INFO HANDLER_TIME %0d %0d %0d %08x %08x %0d", $stime, cluster_id_i, core_id_i, current_task_q.handler_task.msgid, current_task_q.handler_task.handler_fun, current_task_q.handler_task.pkt_addr, current_task_q.handler_task.pkt_size);
            end

            if (handler_error) begin
                $display("[%0d][synt]: HPU (%0d %0d) HANDLER ERROR: %0d", $stime, cluster_id_i, core_id_i, handler_error_code);
            end
        end
    `endif
    // pragma translate_on
endmodule

module cmd_frontend #(
    parameter int unsigned NUM_CMDS         = 4,
    parameter int unsigned NUM_BUFFERED_CMD = 1,
    parameter int unsigned CLUSTER_ID_WIDTH = 16,
    parameter int unsigned CORE_ID_WIDTH    = 16,
    parameter type cmd_req_t                = logic,
    parameter type cmd_resp_t               = logic,
    parameter type dreq_t                   = logic,
    parameter type drsp_t                   = logic
) (
    input logic                        clk_i,
    input logic                        rst_ni,

    input logic [CLUSTER_ID_WIDTH-1:0] cluster_id_i,
    input logic [CORE_ID_WIDTH-1:0]    core_id_i,

    input  dreq_t                      core_req_i,
    output drsp_t                      core_resp_o,

    input  logic                       cmd_resp_valid_i,
    input  cmd_resp_t                  cmd_resp_i,

    input  logic                       disabled_i,
    output logic                       no_pending_cmd_o,

    input  logic                       cmd_ready_i,
    output logic                       cmd_valid_o,
    output cmd_req_t                   cmd_o
);
    `ifdef TODO

    localparam int unsigned ADD_ISSUE = 0;
    localparam int unsigned ADD_WAIT = 1;
    localparam int unsigned ADD_TEST = 2;
    //the rest are of the add_idx are used to define the command to issue

    typedef enum logic [2:0] {Disabled, Ready, WaitingBuffer, WaitingID, Waiting} state_t;
    state_t state_d, state_q;

    //free cmd IDs
    logic [NUM_CMDS-1:0] free_cmd_ids_q;
    logic [NUM_CMDS-1:0] free_cmd_ids_d;

    //core wants to wait/test on the completion of a command
    logic [$clog2(NUM_CMDS)-1:0] wt_cmd_idx;
    logic [$clog2(NUM_CMDS)-1:0] wt_cmd_idx_d;
    logic [$clog2(NUM_CMDS)-1:0] wt_cmd_idx_q;
    logic wt_cmd_finished;

    logic rvalid_d, rvalid_q;
    logic [31:0] rdata_d, rdata_q;

    //current command 
    cmd_req_t cmd_d, cmd_q;
    logic cmd_buff_push;
    logic cmd_buff_empty, cmd_buff_full;

    //index of addressed word
    logic [4:0] add_idx;

    //command index
    logic [$clog2(NUM_CMDS)-1:0] cmd_idx;
    logic no_free_cmd_ids;

    logic trigger_command; //we are ready to send a command (we have an ID, may stall if not cmd_ready_i)

    //command has been issued
    logic cmd_issued;  //core wants to send command (we may stall because no free IDs)
    logic wait_issued; //core wants to wait on a command
    logic test_issued;

    logic assign_id;

    assign cmd_issued  = req_i && add_idx==ADD_ISSUE &&  wen_ni;
    assign wait_issued = req_i && add_idx==ADD_WAIT  && ~wen_ni;
    assign test_issued = req_i && add_idx==ADD_TEST  &&  wen_ni;

    assign add_idx = add_i[6:2];

    assign no_pending_cmd_o = (free_cmd_ids_q == '0);

    //wait/test cmd id
    assign wt_cmd_idx = wdata_i[$clog2(NUM_CMDS)-1:0];
    assign wt_cmd_idx_d = (wait_issued || test_issued) ? wt_cmd_idx : wt_cmd_idx_q;


    assign wt_cmd_finished = (free_cmd_ids_q[wt_cmd_idx_d] == 1'b0) || (cmd_resp_valid_i && cmd_resp_i.cmd_id.local_cmd_id == wt_cmd_idx_d);

    //we push if there is a command and we are not blocking or if we are waiting for the buffer to become non-full
    assign cmd_buff_push = !cmd_buff_full && cmd_issued && state_d==Ready;

    lzc #(
        .WIDTH  (NUM_CMDS)
    ) i_lzc_free_cmd_ids (
        .in_i    (~free_cmd_ids_q),
        .cnt_o   (cmd_idx),
        .empty_o (no_free_cmd_ids)
    );

    fifo_v3 #(
        .dtype     (cmd_req_t),
        .DEPTH     (NUM_BUFFERED_CMD)
    ) i_hpu_cmd_fifo (
        .clk_i     (clk_i),
        .rst_ni    (rst_ni),
        .flush_i   (1'b0),
        .testmode_i(1'b0),
        .full_o    (cmd_buff_full),
        .empty_o   (cmd_buff_empty),
        .usage_o   (),
        .data_i    (cmd_d),
        .push_i    (cmd_buff_push),
        .data_o    (cmd_o),
        .pop_i     (cmd_ready_i && cmd_valid_o)
    ); 

    assign r_rdata_o = rdata_q;
    assign r_valid_o = rvalid_q;

    assign cmd_d.cmd_id.cluster_id = cluster_id_i;
    assign cmd_d.cmd_id.core_id = core_id_i;

    assign cmd_valid_o = !cmd_buff_empty;

    //state transitions
    always_comb begin
        state_d = state_q;
        assign_id = 1'b0;

        case (state_q) 
            Ready: begin
                if (cmd_issued) begin
                    assign_id = 1'b1;
                    if (disabled_i) begin
                        state_d = Disabled;
                        assign_id = 1'b0;
                    end
                    else if (no_free_cmd_ids) begin
                        state_d = WaitingID;
                        assign_id = 1'b0;
                    end
                    else if (cmd_buff_full) begin
                        state_d = WaitingBuffer;
                    end
                end 

                //if the core wants to wait (1) and 
                //the commands is actually marked as in-flight (2) and
                //the current completed command notification (if any) is not for the command the core wants to wait (3)
                if (wait_issued && !wt_cmd_finished) begin
                    state_d = Waiting; 
                end                
            end

            Disabled: begin
                if (!disabled_i) begin
                    assign_id = 1'b1;
                    if (no_free_cmd_ids) begin
                        state_d = WaitingID;
                        assign_id = 1'b0;
                    end
                    else if (cmd_buff_full) begin
                        state_d = WaitingBuffer;
                    end 
                    else begin
                        state_d = Ready;
                    end
                end
            end

            WaitingID: begin
                if (cmd_resp_valid_i) begin
                    state_d = (cmd_buff_full) ? WaitingBuffer : Ready;
                end
            end

            WaitingBuffer: begin
                if (~cmd_buff_full) begin
                    state_d = Ready;
                end
            end

            Waiting: begin
                if (cmd_resp_valid_i && cmd_resp_i.cmd_id.local_cmd_id == wt_cmd_idx_q) begin
                    state_d = Ready;
                end
            end

        endcase
    end

    //free commands
    always_comb begin
        free_cmd_ids_d = free_cmd_ids_q;

        //we assign an ID to a command if there is a command that has been issued and only
        //from the Ready and Disabled states in case there is a di
        if (assign_id) begin
            free_cmd_ids_d[cmd_idx] = 1'b1;
        end

        if (state_q != WaitingID && cmd_resp_valid_i) begin
            free_cmd_ids_d[cmd_resp_i.cmd_id.local_cmd_id] = 1'b0;
        end
    end

    //we reply if we got a request and if this request does not block us or if it unblocks us
    assign rvalid_d = req_i && state_d == Ready;
    assign gnt_o = req_i && state_d == Ready;


    //command registers
    always_comb begin
        cmd_d.descr = cmd_q.descr;
        cmd_d.cmd_type = cmd_q.cmd_type;
        cmd_d.generate_event = cmd_q.generate_event;
        cmd_d.intf_id = cmd_q.intf_id;

        if (req_i && state_q==Ready) begin
            if (add_idx == 3 && ~wen_ni) begin //command definition (type and flags)
                //command type (1:1); generate event flag (0:0)
                /* FIX ME
                case (wdata_i[2:1]) 
                    2'b00: begin
                        cmd_d.cmd_type = HostMemCpy;
                        cmd_d.intf_id  = CMD_EDMA_ID;
                    end
                    2'b01: begin
                        cmd_d.cmd_type = NICSend;
                        cmd_d.intf_id  = CMD_NIC_OUTBOUND_ID;
                    end
                    2'b10: begin
                        cmd_d.cmd_type = HostDirect;
                        cmd_d.intf_id  = CMD_HOSTDIRECT_ID;             
                    end
                endcase
                */
                cmd_d.generate_event = wdata_i[0:0];
             end 
            
            else if (add_idx >= 4 && add_idx <= 10 && ~wen_ni) begin //command definition (words)
                cmd_d.descr.words[add_idx - 4] = wdata_i; 
            end
        end
    end

    //assigning ID to command when issued
    always_comb begin
        cmd_d.cmd_id.local_cmd_id = cmd_q.cmd_id.local_cmd_id;

        case (state_q) 
            WaitingID: begin
                if (cmd_resp_valid_i) begin
                    cmd_d.cmd_id.local_cmd_id = cmd_resp_i.cmd_id.local_cmd_id;
                end
            end
            default: begin
                if (assign_id) begin
                    cmd_d.cmd_id.local_cmd_id = cmd_idx;
                end
            end
        endcase 
    end

    //command issuing
    always_comb begin 
        rdata_d = rdata_q;

        case (state_q) 
            Ready: begin
                if (cmd_issued) begin
                    rdata_d = cmd_idx;
                end

                if (test_issued) begin
                    rdata_d = (wt_cmd_finished) ? 32'h0000_0001 : '0; 
                end
            end

            Waiting: begin
                if (cmd_resp_valid_i) begin
                    rdata_d = cmd_resp_i.cmd_id.local_cmd_id;
                end
            end
        endcase
    end

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
            state_q <= Ready; 
            free_cmd_ids_q <= '0;
            wt_cmd_idx_q <= '0;
            rvalid_q <= 1'b0;
            rdata_q <= '0;
            cmd_q <= '0;
        end else begin
            state_q <= state_d;
            free_cmd_ids_q <= free_cmd_ids_d;
            wt_cmd_idx_q <= wt_cmd_idx_d;
            rvalid_q <= rvalid_d;
            rdata_q <= rdata_d;
            cmd_q <= cmd_d;
        end
    end

    `endif
endmodule
