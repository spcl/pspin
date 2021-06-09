// Copyright (c) 2021 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module task_frontend #(
    parameter int unsigned NUM_CLUSTERS        = 4,
    parameter int unsigned CLUSTER_ID_WIDTH    = 16,
    parameter int unsigned CORE_ID_WIDTH       = 16,
    parameter int unsigned DATA_WIDTH          = 32,
    parameter type hpu_handler_task_t          = logic,
    parameter type task_feedback_descr_t       = logic,
    parameter type dreq_t                      = logic,
    parameter type drsp_t                      = logic,
    parameter type drsp_chan_t                 = logic
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
    input  logic                       can_send_feedback_i,
    output logic                       handler_terminated_o
);

    localparam int unsigned DataAlign = $clog2(DATA_WIDTH/8);

    typedef enum logic [1:0] {Init, Idle, Running, StallingFeedback} state_t;
    state_t state_d, state_q;
    logic [DataAlign-1:0] offset_d, offset_q;

    hpu_handler_task_t current_task_q, current_task_d;

    logic trigger_feedback_d, trigger_feedback_q;

    logic rsp_error;
    logic req_ready;
    logic [31:0] rsp_data;

    logic [$clog2(NUM_CLUSTERS)-1:0] home_cluster_id;

    logic [31:0] l1_home_base_addr;
    logic [31:0] l1_pkt_addr;

    logic [31:0] handler_error_code;
    logic handler_error;

    logic feedback_blocked;

    //buffer feedback waiting for command to complete
    //NOTE: only one feedback at time can be buffered with this implementation!
    task_feedback_descr_t hpu_feedback;
    logic feedback_buff_not_full, feedback_buff_full;
    logic feedback_buff_push;

    logic feedback_buff_out_valid, feedback_buff_out_ready;

    logic core_resp_ready, core_resp_valid;
    drsp_chan_t core_resp;

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
        .valid_o        (feedback_buff_out_valid), 
        .ready_i        (feedback_buff_out_ready) 
    );

    stream_fifo #(
        .FALL_THROUGH(1'b0),
        .DEPTH(2),
        .T(drsp_chan_t)
    ) i_rsp_fifo (
        .clk_i      (clk_i),      
        .rst_ni     (rst_ni),     
        .flush_i    (1'b0),    
        .testmode_i (1'b0), 
        .usage_o    (/*unconnected*/),    
        .data_i     (core_resp),
        .valid_i    (core_resp_valid),
        .ready_o    (core_resp_ready),
        .data_o     (core_resp_o.p), 
        .valid_o    (core_resp_o.p_valid),
        .ready_i    (core_req_i.p_ready) 
    );

    assign feedback_buff_out_ready = can_send_feedback_i && hpu_feedback_ready_i;
    assign hpu_feedback_valid_o = can_send_feedback_i && feedback_buff_out_valid;

    assign feedback_buff_full = ~feedback_buff_not_full;
    assign feedback_buff_push = trigger_feedback_d || (state_q == StallingFeedback);

    // we disable commands if there are feedbacks to send
    assign disable_commands_o = feedback_buff_out_valid;

    assign core_resp.data = rsp_data << {offset_q, 3'b000};
    assign core_resp.error = rsp_error;
    assign core_resp_o.q_ready = req_ready;

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
                if (feedback_blocked) begin
                    state_d = StallingFeedback;
                end 
                else if (trigger_feedback_d) begin
                    state_d = Idle;
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
        req_ready = 1'b0;
        rsp_data = '0;
        handler_error_code = '0;
        handler_error = 1'b0;
        offset_d = offset_q;
        core_resp_valid = 1'b0;
        rsp_error = 1'b0;
        handler_terminated_o = 1'b0;

        trigger_feedback_d = ((state_q == Running && core_req_i.q_valid) || state_q == Idle) ? 1'b0 : trigger_feedback_q;

        if (state_q == Running && core_req_i.q_valid) begin
            req_ready = 1'b1;
            core_resp_valid = 1'b1; /* this gets buffered and delayed upstream */
            offset_d = core_req_i.q.addr[DataAlign-1:0];

            case (core_req_i.q.addr[7:0]) 

                /* Task info */
                8'h00: begin //handler function
                    rsp_data = current_task_q.handler_task.handler_fun; 
                end
                8'h04: begin //handler function size (not needed?)
                    rsp_data = current_task_q.handler_task.handler_fun_size;
                end
                8'h08: begin //handler memory address (L2)
                    rsp_data = current_task_q.handler_task.handler_mem_addr;
                end
                8'h0c: begin //handler memory size 
                    rsp_data = current_task_q.handler_task.handler_mem_size;
                end
                8'h10: begin  //L1 packet address
                    rsp_data = l1_pkt_addr;
                end
                8'h14: begin //packet size
                    rsp_data = current_task_q.handler_task.pkt_size;
                end
                8'h18: begin //scratchpad address 0
                    rsp_data = current_task_q.handler_task.scratchpad_addr[0];
                end
                8'h1c: begin //scratchpad address 1
                    rsp_data = current_task_q.handler_task.scratchpad_addr[1];
                end
                8'h20: begin //scratchpad address 2
                    rsp_data = current_task_q.handler_task.scratchpad_addr[2];
                end
                8'h24: begin //scratchpad address 3
                    rsp_data = current_task_q.handler_task.scratchpad_addr[3];
                end                
                8'h28: begin //scratchpad size 0
                    rsp_data = current_task_q.handler_task.scratchpad_size[0];
                end
                8'h2c: begin //scratchpad size 1
                    rsp_data = current_task_q.handler_task.scratchpad_size[1];
                end
                8'h30: begin //scratchpad size 2
                    rsp_data = current_task_q.handler_task.scratchpad_size[2];
                end
                8'h34: begin //scratchpad size 3
                    rsp_data = current_task_q.handler_task.scratchpad_size[3];
                end
                8'h38: begin //host memory address (high)
                    rsp_data = current_task_q.handler_task.host_mem_addr[63:32];
                end
                8'h3c: begin //host memory address (low)
                    rsp_data = current_task_q.handler_task.host_mem_addr[31:0];
                end
                8'h40: begin //host memory size
                    rsp_data = current_task_q.handler_task.host_mem_size;
                end
                8'h44: begin //L2 packet address
                    rsp_data = current_task_q.handler_task.pkt_addr;
                end
                8'h48: begin //home cluster ID
                    rsp_data = home_cluster_id;
                end
                8'h4c: begin //Message ID
                    rsp_data = current_task_q.handler_task.msgid;
                end

                /* Handler termination */
                8'h50: begin //feedback flag (reading this address leads to the sending of the feedback)
                    rsp_data = '0;
                    trigger_feedback_d = 1'b1;
                    handler_terminated_o = 1'b1;
                end

                /* Handler error */
                8'h54: begin
                    if (core_req_i.q.write) begin
                        handler_error_code = core_req_i.q.data;
                        handler_error = 1'b1;
                    end
                end

                default: begin
                    rsp_error = 1'b1;
                end
            endcase
        end
    end
    
    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
            state_q <= Init; 
            current_task_q <= '0; //how to initialize this?
            trigger_feedback_q <= 1'b0;
            offset_q <= '0;
        end else begin
            state_q <= state_d;
            current_task_q <= current_task_d;
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