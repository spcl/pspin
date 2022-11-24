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

module mpq_engine #(
    parameter int NUM_HER_SLOTS = 64,
    parameter int NUM_MPQ = 8
)
(
    input   logic              clk_i,
    input   logic              rst_ni,

    //from pkt gen
    output logic               her_ready_o,
    input  logic               her_valid_i,
    input  her_descr_t         her_i,
    
    //termination signal    
    input  logic               eos_i,

    //mpq ready signal
    output logic [NUM_MPQ-1:0] mpq_full_o,

    //from feedback engine
    output logic               feedback_ready_o,
    input  logic               feedback_valid_i,
    input  feedback_descr_t    feedback_i,

    //to scheduler
    input  logic               task_ready_i,
    output logic               task_valid_o,
    output handler_task_t      task_o,

    //to pktgen
    input logic                nic_feedback_ready_i,
    output logic               nic_feedback_valid_o,
    output feedback_descr_t    nic_feedback_o
);
    typedef struct packed {
        mem_addr_t pkt_addr;
        mem_size_t pkt_size;
    } mpq_pkt_t;

    localparam int unsigned MPQ_META_LEN   = $bits(mpq_meta_t);
    localparam int unsigned MPQ_META_LEN_B = MPQ_META_LEN/8;

    // MPQ engine state. This is mainly to handle the case in which
    // task_ready_i is not asserted and enable pipelining between
    // reading from MPQ meta memory and defining output task
    typedef enum logic [2:0] {Idle, Ready, Stalled} mpqeng_state_t;
    mpqeng_state_t state_q, state_d;

    // MPQ state. I don't think we can move this too to memory :(
    mpq_t [NUM_MPQ-1:0] mpq_q;
    mpq_t [NUM_MPQ-1:0] mpq_d;

    // Flag saying if an MPQ is ready or not
    logic [NUM_MPQ-1:0] mpq_valid;

    // Flag saying if an MPQ is being used or not
    logic [NUM_MPQ-1:0] mpq_busy;

    // ID of the MPQ for which we received a new HER
    logic [$clog2(NUM_MPQ)-1:0] newher_mpq_idx;

    // ID of the MPQ which we are sending a task from
    logic [$clog2(NUM_MPQ)-1:0] tasksent_mpq_idx;

    // ID of the MPQ for which we received a task
    logic [$clog2(NUM_MPQ)-1:0] feedback_mpq_idx;

    // aribitrate ready MPQs
    logic [$clog2(NUM_MPQ)-1:0] mpq_arb_idx;

    // Next packet to schedule for each MPQ
    mpq_pkt_t mpq_head;

    // New packet to push in the fifo_engine
    mpq_pkt_t new_pkt;

    // We store the handler_task in order to use it in case we get stalled
    handler_task_t task_q, task_d, new_task;

    // We use these registers to rember info about the currently selected MPQ.
    // We need to way one cycle to get the output from memory and use that,
    // toghether with these info, to build the output. 
    mpq_state_t mpq_out_state_d, mpq_out_state_q;
    logic [$clog2(NUM_MPQ)-1:0] selected_mpq_d;
    logic [$clog2(NUM_MPQ)-1:0] selected_mpq_q;

    // push/pop drivers for FIFO engine
    logic fifo_push, fifo_pop;

    // flag saying if the FIFO engine is empty of full
    // NOTE: fifo_empty is only used in assertions
    logic fifo_empty;
    logic [NUM_MPQ-1:0] fifo_full;

    // Updated MPQs from the FSMs output
    mpq_t newher_mpq_fsm_s, tasksent_mpq_fsm_s, feedback_mpq_fsm_s;

    // Flags saying if the FSMs' output is valid
    logic newher_mpq_fsm_update, tasksent_mpq_fsm_update, feedback_mpq_fsm_update;

    // True if we are writing to the MPQ meta memory
    logic mpqmeta_write;

    // True if we are reading from MPQ meta memory
    logic mpqmeta_read;

    // Flag used in the defintion of the output task (ugly).
    logic new_task_triggers_feedback_q, new_task_triggers_feedback_d;

    // Read output of the MPQ meta memory
    mpq_meta_t mpqmeta_read_mpq;
    mpq_meta_t mpqmeta_read_mpq_ignored; 

    // ready/valid for arbiter 
    logic arb_ready, arb_valid;

    assign mpq_full_o = fifo_full;

    // define the MPQ indices for the different events
    assign newher_mpq_idx      = her_i.msgid[$clog2(NUM_MPQ)-1:0];
    assign tasksent_mpq_idx    = mpq_arb_idx; //this one comes one cycle before task_o! 
    assign feedback_mpq_idx    = feedback_i.msgid[$clog2(NUM_MPQ)-1:0];

    // Here we store the packets that are queued for each MPQ
    assign new_pkt.pkt_addr = her_i.her_addr;
    assign new_pkt.pkt_size = her_i.xfer_size;

    assign fifo_push = her_ready_o && her_valid_i;

    // Note: this is quite ugly, should be fixed.
    assign fifo_pop  = (arb_ready && arb_valid && (
                        (mpq_q[tasksent_mpq_idx].state == Payload && mpq_d[tasksent_mpq_idx].state == Payload) || /* pop payload packets but not the eom */
                        (mpq_q[tasksent_mpq_idx].state == Payload && mpq_d[tasksent_mpq_idx].state == PayloadDraining && !mpq_d[tasksent_mpq_idx].has_completion) || /* pop eom already if there is no completion handler */
                        (mpq_q[tasksent_mpq_idx].state == Completion) /* pop EOM when the completion is sent */
                       ));

    fifo_engine #(
        .NUM_CELLS(NUM_HER_SLOTS),
        .NUM_STATIC_CELLS_PER_FIFO(NUM_MPQ_STATIC_CELLS),
        .NUM_FIFO(NUM_MPQ),
        .elem_t(mpq_pkt_t)
    ) i_fifo_engine (
        .clk_i              (clk_i),
        .rst_ni             (rst_ni),
        .new_el_i           (new_pkt),
        .push_i             (fifo_push),
        .fifo_push_id_i     (newher_mpq_idx),
        .pop_i              (fifo_pop),
        .fifo_pop_id_i      (tasksent_mpq_idx),
        .data_o             (mpq_head),
        .empty_o            (fifo_empty),
        .fifo_full_o        (fifo_full)
    );

    // MPQ metadata memory
    assign mpqmeta_write = her_valid_i && her_ready_o && !mpq_busy[newher_mpq_idx];
    assign mpqmeta_read = arb_ready && arb_valid;

    tc_sram #(
        .NumWords   (NUM_MPQ),
        .DataWidth  (MPQ_META_LEN),
        .NumPorts   (2)
    ) i_mpq_meta_mem (
        .clk_i      (clk_i),
        .rst_ni     (rst_ni),
        .req_i      ({mpqmeta_write, mpqmeta_read}),
        .we_i       ({mpqmeta_write, 1'b0}),
        .addr_i     ({newher_mpq_idx, tasksent_mpq_idx}),
        .wdata_i    ({her_i.mpq_meta, {MPQ_META_LEN{1'b0}}}),
        .be_i       ({{MPQ_META_LEN_B{1'b1}}, {MPQ_META_LEN_B{1'b0}}}),
        .rdata_o    ({mpqmeta_read_mpq_ignored, mpqmeta_read_mpq})
    );

    // Select a ready MPQ
    rr_arb_tree #(
        .NumIn      (NUM_MPQ),
        .DataWidth  (0),
        .ExtPrio    (0),
        .AxiVldRdy  (1),
        .LockIn     (1)
    ) i_mpq_rr_arb (
        .clk_i      (clk_i),
        .rst_ni     (rst_ni),
        .flush_i    (1'b0),
        .rr_i       ('0),
        .req_i      (mpq_valid),
        .gnt_o      (),
        .data_i     (),
        .gnt_i      (arb_ready),
        .req_o      (arb_valid),
        .data_o     (),
        .idx_o      (mpq_arb_idx)
    );

    // Define state
    always_comb begin
        state_d = state_q;
        arb_ready = 1'b0;

        case (state_q)
            Idle: begin
                if (arb_valid == 1'b1) begin
                    state_d = Ready;
                    arb_ready = 1'b1;
                end
            end
            Ready: begin
                if (task_ready_i == 1'b0) begin
                    state_d = Stalled;
                end else begin
                    state_d = (arb_valid == 1'b1) ? Ready : Idle;
                    arb_ready = (arb_valid == 1'b1);
                end
            end
            Stalled: begin
                if (task_ready_i == 1'b1) begin
                    state_d = (arb_valid == 1'b1) ? Ready : Idle;
                    arb_ready = (arb_valid == 1'b1); //to pipeline next memory read
                end
            end
        endcase
    end

    // Define output
    // we delay mpq_arb_idx because the the memory read output will be
    // ready at the next cycle

    assign task_valid_o = (state_q == Ready || state_q == Stalled);

    //this seems overworked.. 
    assign task_o = (state_q==Ready) ? new_task : task_q;
    assign task_d = (state_q==Ready) ? new_task : task_q;

    assign mpq_out_state_d = (arb_ready && arb_valid) ? mpq_q[tasksent_mpq_idx].state : mpq_out_state_q;
    assign selected_mpq_d = (arb_ready && arb_valid) ? tasksent_mpq_idx : selected_mpq_q;
    assign new_task_triggers_feedback_d = (arb_ready && arb_valid) ? fifo_pop : new_task_triggers_feedback_q;

    always_comb begin 
        case (mpq_out_state_q)
            Header: begin
                new_task.handler_fun = mpqmeta_read_mpq.hh_addr;
                new_task.handler_fun_size = mpqmeta_read_mpq.hh_size;
                new_task.pkt_addr = mpq_head.pkt_addr;
                new_task.pkt_size = mpq_head.pkt_size;
                new_task.trigger_feedback = new_task_triggers_feedback_q;
            end

            Payload: begin
                new_task.handler_fun = mpqmeta_read_mpq.ph_addr;
                new_task.handler_fun_size = mpqmeta_read_mpq.ph_size;
                new_task.pkt_addr = mpq_head.pkt_addr;
                new_task.pkt_size = mpq_head.pkt_size;
                new_task.trigger_feedback = new_task_triggers_feedback_q;
            end

            Completion: begin
                new_task.handler_fun = mpqmeta_read_mpq.th_addr;
                new_task.handler_fun_size = mpqmeta_read_mpq.th_size;
                new_task.pkt_addr = mpq_head.pkt_addr;
                new_task.pkt_size = mpq_head.pkt_size;
                new_task.trigger_feedback = new_task_triggers_feedback_q;
            end

            default: begin
                new_task.handler_fun = '0;
                new_task.handler_fun_size = '0;
                new_task.pkt_addr = '0;
                new_task.pkt_size = '0;
                new_task.trigger_feedback = 1'b0;
            end
        endcase
    end

    assign new_task.msgid            = selected_mpq_q;
    assign new_task.handler_mem_addr = mpqmeta_read_mpq.handler_mem_addr;
    assign new_task.handler_mem_size = mpqmeta_read_mpq.handler_mem_size;
    assign new_task.host_mem_addr    = mpqmeta_read_mpq.host_mem_addr;
    assign new_task.host_mem_size    = mpqmeta_read_mpq.host_mem_size;
    
    for (genvar i = 0; i< pspin_cfg_pkg::NUM_CLUSTERS; i++) begin: gen_task_scratchpad
        assign new_task.scratchpad_addr[i] = mpqmeta_read_mpq.scratchpad_addr[i];
        assign new_task.scratchpad_size[i] = mpqmeta_read_mpq.scratchpad_size[i];
    end
    
    // Update MPQ state
    // This unit might have to process at most three MPQs at the same time:
    // - the MPQ for which we get a new HER,
    // - the MPQ for which we get a completion feedback,
    // - the MPQ that gets selected to send a new task.
    // For this reason, we keep three mpq_fsm. It can happen that two or all FSM
    // will be fed with the same MPQ (e.g., getting a new HER and a completion feedback
    // for the same MPQ in the same cycle). In that case, the FSM will produce the same
    // output state, so it does not matter which output gets written. 
    mpq_fsm #(
    ) i_newher_mpq_fsm (
        .her_new_i          (her_valid_i && her_ready_o),
        .task_sent_i        (arb_valid && arb_ready && tasksent_mpq_idx == newher_mpq_idx),
        .feedback_i         (feedback_valid_i && feedback_ready_o && feedback_mpq_idx == newher_mpq_idx),

        .her_new_has_hh_i   (her_i.mpq_meta.hh_addr != '0),
        .her_new_has_th_i   (her_i.mpq_meta.th_addr != '0),
        .her_new_is_eom_i   (her_i.eom),

        .mpq_q              (mpq_q[newher_mpq_idx]),
        .mpq_o              (newher_mpq_fsm_s),

        .update_o           (newher_mpq_fsm_update)
    );

    mpq_fsm #(
    ) i_tasksent_mpq_fsm (
        .her_new_i          (her_valid_i && her_ready_o && newher_mpq_idx == tasksent_mpq_idx),
        .task_sent_i        (arb_valid && arb_ready),
        .feedback_i         (feedback_valid_i && feedback_ready_o && feedback_mpq_idx == tasksent_mpq_idx),

        .her_new_has_hh_i   (her_i.mpq_meta.hh_addr != '0),
        .her_new_has_th_i   (her_i.mpq_meta.th_addr != '0),
        .her_new_is_eom_i   (her_i.eom),

        .mpq_q              (mpq_q[tasksent_mpq_idx]),
        .mpq_o              (tasksent_mpq_fsm_s),

        .update_o           (tasksent_mpq_fsm_update)
    );

    mpq_fsm #(
    ) i_feedback_mpq_fsm (
        .her_new_i          (her_valid_i && her_ready_o && newher_mpq_idx == feedback_mpq_idx),
        .task_sent_i        (arb_valid && arb_ready && feedback_mpq_idx == tasksent_mpq_idx),
        .feedback_i         (feedback_valid_i && feedback_ready_o),

        .her_new_has_hh_i   (her_i.mpq_meta.hh_addr != '0),
        .her_new_has_th_i   (her_i.mpq_meta.th_addr != '0),
        .her_new_is_eom_i   (her_i.eom),

        .mpq_q              (mpq_q[feedback_mpq_idx]),
        .mpq_o              (feedback_mpq_fsm_s),

        .update_o           (feedback_mpq_fsm_update)
    );

    always_comb begin
        mpq_d = mpq_q;

        if (newher_mpq_fsm_update) begin
            mpq_d[newher_mpq_idx] = newher_mpq_fsm_s;
        end

        if (tasksent_mpq_fsm_update) begin
            mpq_d[tasksent_mpq_idx] = tasksent_mpq_fsm_s;
        end

        if (feedback_mpq_fsm_update) begin
            mpq_d[feedback_mpq_idx] = feedback_mpq_fsm_s;
        end
    end

    // Define valid/busy MPQs
    for (genvar i=0; i<NUM_MPQ; i++) begin
        assign mpq_valid[i] = ((mpq_q[i].state == Header) || 
                               (mpq_q[i].state == Payload && mpq_q[i].length > 0) || 
                               (mpq_q[i].state == Completion));
        assign mpq_busy[i]  = (mpq_q[i].state != Free);
    end

    // Define ready signal on the HER input interface. We can 
    // get a new HER if the MPQ to which the HER will go has space. 
    assign her_ready_o = !fifo_full[newher_mpq_idx]; //((~fifo_full) != '0);

    // Forward the feedback to the NIC inbound engine
    assign feedback_ready_o     = nic_feedback_ready_i;
    assign nic_feedback_valid_o = feedback_valid_i && feedback_i.trigger_feedback == 1'b1;
    assign nic_feedback_o       = feedback_i;

    // Sequential 
    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
            mpq_q <= '0;
            selected_mpq_q <= '0;
            state_q <= Idle;
            mpq_out_state_q <= Free;
            task_q <= '0;
            new_task_triggers_feedback_q <= 1'b0;
        end else begin
            mpq_q <= mpq_d;
            selected_mpq_q <= selected_mpq_d;
            state_q <= state_d;
            mpq_out_state_q <= mpq_out_state_d;
            task_q <= task_d;
            new_task_triggers_feedback_q <= new_task_triggers_feedback_d;
        end
    end

    // Simulation only
    // pragma translate_off
    `ifndef VERILATOR
    initial begin
        forever begin
            @(posedge clk_i);
            if (feedback_ready_o && feedback_valid_i) begin
                $display("%0d MPQ engine got feedback for msg id %0d", $time, feedback_i.msgid);
            end

            if (her_ready_o && her_valid_i) begin
                $display("%0d MPQ engine got new packet for msg id %0d", $time, her_i.msgid);
            end

        end
    end

    // Assertions
    nonempty : assert property(
      @(posedge clk_i) (mpq_busy=='0 && eos_i) |-> (fifo_empty))
        else $fatal (1, "Termination detected but there still are packets to process!");

    for (genvar i=0; i<NUM_MPQ; i++) begin
        negativelength: assert property(
            @(posedge clk_i) (mpq_q[i].length == '0) |-> (~(mpq_d[i].length) != '0))
            else $fatal (1, "MPQ length is negative!");

        negativeinflight: assert property(
            @(posedge clk_i) (mpq_q[i].in_flight == '0) |-> (~(mpq_d[i].in_flight) != '0))
            else $fatal (1, "MPQ in_flight is negative!");
    end
    `endif
    // pragma translate_on


endmodule 

module mpq_fsm #(
) (

    // events
    input logic     her_new_i,          // got a new HER
    input logic     task_sent_i,        // got selected for sending a task
    input logic     feedback_i,         // got a completion feedback

    //info on the new HER, if any (used only if her_new_i is asserted)
    input  logic    her_new_has_hh_i,   // Asserted if the new HER as a header handler
    input  logic    her_new_has_th_i,   // Asserted if the new HER as a completion handler
    input  logic    her_new_is_eom_i,   // Asserted if the new HER is flagged as EOM

    input  mpq_t    mpq_q,              // current state
    output mpq_t    mpq_o,              // new state

    output logic    update_o            // asserted if mpq_o is valid
);

    logic pushing_her, popping_her;
    assign pushing_her = her_new_i;
    assign popping_her = (task_sent_i && mpq_q.state == Payload);

    assign update_o = her_new_i || task_sent_i || feedback_i;

    //update MPQ length
    always_comb begin
        case ({pushing_her, popping_her})
            2'b10   : mpq_o.length = mpq_q.length + 1;
            2'b01   : mpq_o.length = mpq_q.length - 1;
            default : mpq_o.length = mpq_q.length;
        endcase
    end

    always_comb begin 
        case ({task_sent_i, feedback_i})
            2'b10   : mpq_o.in_flight = mpq_q.in_flight + 1;
            2'b01   : mpq_o.in_flight = mpq_q.in_flight - 1;
            default : mpq_o.in_flight = mpq_q.in_flight;
        endcase
    end

    always_comb begin
        mpq_o.eom_seen = mpq_q.eom_seen;

        // set it if we see the EOM
        if (her_new_i && her_new_is_eom_i) begin
            mpq_o.eom_seen = 1;
        end

        // clear it if we are transitioning to Free state
        if (mpq_o.state == Free) begin
            mpq_o.eom_seen = 0;
        end
    end

    //update state
    always_comb begin //H-P-C case

        mpq_o.state = mpq_q.state;
        mpq_o.has_completion = mpq_q.has_completion;

        case (mpq_q.state) 
            Free: begin
                if (her_new_i) begin
                    mpq_o.state = (her_new_has_hh_i) ? Header : Payload;
                    mpq_o.has_completion = her_new_has_th_i;
                end
            end

            Header: begin
                if (task_sent_i) begin
                    mpq_o.state = HeaderRunning;
                end
            end 

            HeaderRunning: begin
                if (feedback_i) begin
                    mpq_o.state = Payload;
                end
            end
    
            Payload: begin
                if (task_sent_i && mpq_q.eom_seen && mpq_q.length == 1) begin
                    mpq_o.state = PayloadDraining;
                end
            end

            PayloadDraining: begin
                if (feedback_i && mpq_q.in_flight == 1) begin
                    mpq_o.state = (mpq_q.has_completion) ? Completion : Free;
                end
            end

            Completion: begin
                if (task_sent_i) begin
                    mpq_o.state = CompletionRunning;
                end
            end

            CompletionRunning: begin
                if (feedback_i) begin
                    mpq_o.state = Free;
                end
            end
        endcase
    end
endmodule
