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

module hpu_driver #(
    parameter int C_CORE_ID            = 0,
    parameter int L1_PKT_BUFF_SIZE     = 512,
    parameter int NUM_CLUSTERS         = 4,
    parameter int NUM_SCRATCHPADS      = 1,
    parameter int NUM_HERS_PER_CLUSTER = 1,
    parameter int L1_CLUSTER_BASE      = 0,
    parameter int L1_CLUSTER_MEM_SIZE  = 0,
    parameter int L1_RUNTIME_OFFSET    = 0,
    parameter int L1_SCRATCHPAD_SIZE   = 4096,
    parameter int NUM_CMDS             = 4,
    parameter int N_PMP_ENTRIES        = 16
) (
    input logic                   clk_i,
    input logic                   rst_ni,

    input logic [5:0]             cluster_id_i,

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
    XBAR_PERIPH_BUS.Slave         hpu_driver_slave_i,

    //high if this core has no pending DMA requests
    input logic                   no_dma_req_pending_i,

    //command out
    input  logic                  cmd_ready_i,
    output logic                  cmd_valid_o,
    output pspin_cmd_t            cmd_o,

    //command completion notification in
    input  logic                  cmd_resp_valid_i,
    input  pspin_cmd_resp_t       cmd_resp_i,

    //PMP configuration
    output logic pmp_conf_override_o,
    output logic [N_PMP_ENTRIES-1:0] [31:0] pmp_addr_o,
    output logic [N_PMP_ENTRIES-1:0] [7:0]  pmp_cfg_o
);

    logic no_pending_cmd;

    //request destination: 0: task_frontend; 1: cmd_frontend;
    logic [1:0] add_type_d;
    logic [1:0] add_type_q;
    assign add_type_d = hpu_driver_slave_i.add[8:7];

    //word idx (max 32 words per add_type)
    //logic [4:0] add_idx;
    //assign add_idx = hpu_driver_slave_i.add[6:2];

    //tf: task frontend; cf: cmd frontend
    logic [3:0]       frontend_req;
    logic [3:0]       frontend_gnt;
    logic [3:0]       frontend_r_valid;
    logic [3:0][31:0] frontend_r_rdata;

    logic can_send_feedback;
    logic cmd_resp_valid;
    logic disable_commands;

    //NOTE: frontends 2 and 3 are unused (reserved for future extensions)
    for (genvar i=0; i<4; i++) begin
        assign frontend_req[i] = hpu_driver_slave_i.req && (add_type_d == i);
    end

    for (genvar i=2; i<4; i++) begin
        assign frontend_gnt[i] = 1'b0;
        assign frontend_r_valid[i] = 1'b0;
        assign frontend_r_rdata[i] = '0;
    end

    assign hpu_driver_slave_i.gnt     = frontend_gnt[add_type_d];

    //we need to remember which output to pick because this will (eventually)
    //be valid at the next cycle.
    assign hpu_driver_slave_i.r_rdata = frontend_r_rdata[add_type_q];
    assign hpu_driver_slave_i.r_valid = frontend_r_valid[add_type_q];

    assign can_send_feedback = no_dma_req_pending_i && no_pending_cmd;

    assign cmd_resp_valid = cmd_resp_valid_i && cmd_resp_i.cmd_id.cluster_id == cluster_id_i && cmd_resp_i.cmd_id.core_id == C_CORE_ID;

    task_frontend #(
        .C_CORE_ID                 (C_CORE_ID),
        .L1_PKT_BUFF_SIZE          (L1_PKT_BUFF_SIZE),
        .NUM_CLUSTERS              (NUM_CLUSTERS),
        .NUM_SCRATCHPADS           (NUM_SCRATCHPADS),
        .NUM_HERS_PER_CLUSTER      (NUM_HERS_PER_CLUSTER),
        .L1_CLUSTER_BASE           (L1_CLUSTER_BASE),
        .L1_CLUSTER_MEM_SIZE       (L1_CLUSTER_MEM_SIZE),
        .L1_RUNTIME_OFFSET         (L1_RUNTIME_OFFSET),
        .L1_SCRATCHPAD_SIZE        (L1_SCRATCHPAD_SIZE),
        .N_PMP_ENTRIES             (N_PMP_ENTRIES)
    ) i_task_frontend (
        .clk_i                     (clk_i),
        .rst_ni                    (rst_ni),
        .cluster_id_i              (cluster_id_i),
        .hpu_task_valid_i          (hpu_task_valid_i),
        .hpu_task_ready_o          (hpu_task_ready_o),
        .hpu_task_i                (hpu_task_i),
        .hpu_feedback_valid_o      (hpu_feedback_valid_o),
        .hpu_feedback_ready_i      (hpu_feedback_ready_i),
        .hpu_feedback_o            (hpu_feedback_o),
        .hpu_active_o              (hpu_active_o),
        .req_i                     (frontend_req[0]),
        .add_i                     (hpu_driver_slave_i.add),
        .wen_ni                    (hpu_driver_slave_i.wen),
        .wdata_i                   (hpu_driver_slave_i.wdata),
        .be_i                      (hpu_driver_slave_i.be),
        .gnt_o                     (frontend_gnt[0]),
        .r_rdata_o                 (frontend_r_rdata[0]),
        .r_valid_o                 (frontend_r_valid[0]),
        .can_send_feedback_i       (can_send_feedback),
        .pmp_conf_override_o       (pmp_conf_override_o),
        .pmp_cfg_o                 (pmp_cfg_o),
        .pmp_addr_o                (pmp_addr_o),
        .disable_commands_o        (disable_commands)
    );

    cmd_frontend #(
        .C_CORE_ID                 (C_CORE_ID),
        .NUM_CMDS                  (NUM_CMDS),
        .NUM_BUFFERED_CMD          (NUM_CMDS)
    ) i_cmd_frontend (
        .clk_i                     (clk_i),
        .rst_ni                    (rst_ni),
        .cluster_id_i              (cluster_id_i),
        .req_i                     (frontend_req[1]),
        .add_i                     (hpu_driver_slave_i.add),
        .wen_ni                    (hpu_driver_slave_i.wen),
        .wdata_i                   (hpu_driver_slave_i.wdata),
        .be_i                      (hpu_driver_slave_i.be),
        .gnt_o                     (frontend_gnt[1]),
        .r_rdata_o                 (frontend_r_rdata[1]),
        .r_valid_o                 (frontend_r_valid[1]),

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
            add_type_q <= '0;
        end else begin
            add_type_q <= add_type_d;
        end
    end

endmodule


module task_frontend #(
    parameter int C_CORE_ID            = 0,
    parameter int L1_PKT_BUFF_SIZE     = 512,
    parameter int NUM_CLUSTERS         = 4,
    parameter int NUM_SCRATCHPADS      = 1,
    parameter int NUM_HERS_PER_CLUSTER = 1,
    parameter int L1_CLUSTER_BASE      = 0,
    parameter int L1_CLUSTER_MEM_SIZE  = 0,
    parameter int L1_RUNTIME_OFFSET    = 0,
    parameter int L1_SCRATCHPAD_SIZE   = 4096,
    parameter int N_PMP_ENTRIES        = 16
) (
    input logic                   clk_i,
    input logic                   rst_ni,

    input logic [5:0]             cluster_id_i,

    //task in
    input  logic                  hpu_task_valid_i,
    output logic                  hpu_task_ready_o, 
    input  hpu_handler_task_t     hpu_task_i,

    //feedback out
    output logic                  hpu_feedback_valid_o,
    input  logic                  hpu_feedback_ready_i,
    output task_feedback_descr_t  hpu_feedback_o,

    output logic                  hpu_active_o,

    input  logic                  req_i,
    input  logic [31:0]           add_i,
    input  logic                  wen_ni,
    input  logic [31:0]           wdata_i,
    input  logic [3:0]            be_i,
    output logic                  gnt_o,
    output logic [31:0]           r_rdata_o,
    output logic                  r_valid_o,

    output logic                  disable_commands_o,
    input  logic                  can_send_feedback_i,

    output logic                  pmp_conf_override_o,
    output logic                  [N_PMP_ENTRIES-1:0] [31:0] pmp_addr_o,
    output logic                  [N_PMP_ENTRIES-1:0] [7:0]  pmp_cfg_o
);

    typedef enum logic [1:0] {Init, Idle, Running, SendingFeedback} state_t;
    state_t state_d, state_q;

    hpu_handler_task_t current_task_q, current_task_d;

    logic trigger_feedback;

    logic valid_d, valid_q;
    logic [31:0] rdata_d, rdata_q;

    logic [$clog2(NUM_SCRATCHPADS)-1:0] scratchpad_id;
    logic [$clog2(NUM_CLUSTERS)-1:0] home_cluster_id;

    logic [31:0] l1_pkt_base_addr; // in this cluster
    logic [NUM_CLUSTERS-1:0][31:0] l1_scratchpad_addr; //in the home cluster

    logic [31:0] l1_base_addr;
    logic [31:0] l1_home_base_addr;
    logic [31:0] l1_pkt_addr;

    logic [N_PMP_ENTRIES-1:0] [31:0] pmp_addr_q;
    logic [N_PMP_ENTRIES-1:0] [31:0] pmp_addr_d;
    logic [N_PMP_ENTRIES-1:0] [7:0]  pmp_cfg_q;
    logic [N_PMP_ENTRIES-1:0] [7:0]  pmp_cfg_d;


    logic [31:0] handler_error_code;
    logic handler_error;

    //buffer feedback waiting for command to complete
    //NOTE: only one feedback at time can be buffered with this implementation!
    task_feedback_descr_t hpu_feedback;
    logic feedback_buff_full, feedback_buff_empty;
    logic feedback_buff_push;
    fifo_v3 #(
        .dtype     (task_feedback_descr_t),
        .DEPTH     (1)
    ) i_hpu_cmd_fifo (
        .clk_i     (clk_i),
        .rst_ni    (rst_ni),
        .flush_i   (1'b0),
        .testmode_i(1'b0),
        .full_o    (feedback_buff_full),
        .empty_o   (feedback_buff_empty),
        .usage_o   (),
        .data_i    (hpu_feedback),
        .push_i    (feedback_buff_push),
        .data_o    (hpu_feedback_o),
        .pop_i     (hpu_feedback_ready_i && hpu_feedback_valid_o)
    ); 

    assign feedback_buff_push = !feedback_buff_full && (trigger_feedback || state_q==SendingFeedback);
    assign disable_commands_o = !feedback_buff_empty;

    assign r_rdata_o = rdata_q;
    assign r_valid_o = valid_q;

    //this way of determining addresses is super ugly but don't know how to make it nicer
    assign scratchpad_id = current_task_q.handler_task.msgid[$clog2(NUM_CLUSTERS)+$clog2(NUM_SCRATCHPADS)-1:$clog2(NUM_CLUSTERS)];
    assign home_cluster_id = current_task_q.handler_task.msgid[$clog2(NUM_CLUSTERS)-1:0];
    assign l1_base_addr = (L1_CLUSTER_BASE + cluster_id_i * L1_CLUSTER_MEM_SIZE);
    assign l1_pkt_base_addr = l1_base_addr + L1_RUNTIME_OFFSET;
    assign l1_pkt_addr = current_task_q.pkt_ptr;

    for (genvar i=0; i<NUM_CLUSTERS; i++) begin: gen_scratchpad_addresses
        assign l1_scratchpad_addr[i] = L1_CLUSTER_BASE + (i * L1_CLUSTER_MEM_SIZE) + L1_SCRATCHPAD_OFFSET + current_task_q.handler_task.scratchpad_addr[i];
    end

    //building feedback
    assign hpu_feedback.pkt_ptr                         = current_task_q.pkt_ptr;
    assign hpu_feedback.feedback_descr.pkt_addr         = current_task_q.handler_task.pkt_addr;
    assign hpu_feedback.feedback_descr.msgid            = current_task_q.handler_task.msgid;
    assign hpu_feedback.feedback_descr.pkt_size         = current_task_q.handler_task.pkt_size;
    assign hpu_feedback.feedback_descr.trigger_feedback = current_task_q.handler_task.trigger_feedback;

    assign hpu_task_ready_o = (state_q == Idle);
    assign hpu_feedback_valid_o = can_send_feedback_i && !feedback_buff_empty;

    assign hpu_active_o = state_q != Init;

    //TODO: this whole part needs to be fixed. I'm whitelisting more than needed.
    assign pmp_conf_override_o = 1'b1;
    assign pmp_addr_o = pmp_addr_q;
    assign pmp_cfg_o = pmp_cfg_q;

    //PMP configuration: L - WIRI(2) - A(2) - X - W -R

    // PMP: runtime code
    //I'm giving the full program code for now
    //TODO: get runtime address/size correctly
    assign pmp_cfg_d[0] = 8'b0_00_11_1_0_1;
    assign pmp_addr_d[0] = 32'h1d07_FFFF;

    // PMP: stack
    //TODO: get stack address correctly
    //TODO: there is no point in keeping the configuration in a FF.
    assign pmp_cfg_d[1] = 8'b0_00_11_0_1_1;
    assign pmp_addr_d[1][31:24] = l1_base_addr[31:24];
    assign pmp_addr_d[1][23:0] = 24'h7F_FFFF;

    // PMP: peripherals 
    assign pmp_cfg_d[2] = 8'b0_00_11_0_1_1;
    assign pmp_addr_d[2] = 32'h1b7F_FFFF;

    // PMP: packet memory (L1)
    assign pmp_cfg_d[3] = 8'b0_00_11_0_1_1;
    assign pmp_addr_d[3][31:12] = l1_pkt_addr[31:12];
    assign pmp_addr_d[3][11:0] = 12'h7FF; // 4 KiB TODO: fix

    // PMP: packet memory (L2)
    assign pmp_cfg_d[4] = 8'b0_00_11_0_1_1;
    assign pmp_addr_d[4][31:12] = current_task_q.handler_task.pkt_addr[31:12];
    assign pmp_addr_d[4][11:0] = 12'h7FF; // 4 KiB TODO: fix

    // PMP: handler code
    assign pmp_cfg_d[5] = 8'b0_00_11_1_0_1;
    assign pmp_addr_d[5][31:12] = current_task_q.handler_task.handler_fun[31:12];
    assign pmp_addr_d[5][11:0] = 12'h7FF; // 4 KiB TODO: fix

    // PMP: handler memory
    assign pmp_cfg_d[6] = 8'b0_00_11_0_1_1;
    assign pmp_addr_d[6][31:20] = current_task_q.handler_task.handler_mem_addr[31:20];
    assign pmp_addr_d[6][19:0]  = 20'h7FFFF; // 4 MiB TODO: fix

    // PMP: stdout virtual device
    assign pmp_cfg_d[7] = 8'b0_00_11_0_1_0;
    assign pmp_addr_d[7][31:0] = 32'h1a10_7fff;
 
    // PMP: beginning of L2 handler memory (for, e.g., .rodata)
    assign pmp_cfg_d[8] = 8'b0_00_11_0_1_1;
    assign pmp_addr_d[8][31:0] = 32'h1c00_7fff;

    for (genvar i=0; i<NUM_CLUSTERS; i++) begin : gen_pmp_scratchpad
        assign pmp_cfg_d[9+i] = 8'b0_00_11_0_1_1;
        assign pmp_addr_d[9+i][31:12] = l1_scratchpad_addr[i][31:12];
        assign pmp_addr_d[9+i][11:0] = 12'h7FF; // 4 KiB TODO: fix
    end

    for (genvar i=9+NUM_CLUSTERS; i<N_PMP_ENTRIES; i++) begin
        assign pmp_cfg_d[i] = '0;
        assign pmp_addr_d[i] = '0;
    end

    always_comb begin
        state_d = state_q;
        current_task_d = current_task_q;

        case (state_q)
            Init: begin
                if (req_i) begin
                    state_d = Idle;
                end
            end
            Idle: begin
                if (hpu_task_valid_i) begin
                    state_d = (hpu_task_i.handler_task.handler_fun == '0) ? SendingFeedback : Running;
                    current_task_d = hpu_task_i;
                end
            end 

            Running: begin 
                if (trigger_feedback) begin
                    state_d = (feedback_buff_full) ? SendingFeedback : Idle;
                end
            end

            SendingFeedback: begin
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
        gnt_o = 1'b0;    
        trigger_feedback = 1'b0;
        rdata_d = rdata_q;
        valid_d = 1'b0;
        handler_error_code = '0;
        handler_error = 1'b0;

        if (state_q == Running && req_i) begin
            gnt_o = 1'b1;     
            valid_d = 1'b1;
            
            case (add_i[7:0]) 

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
                    rdata_d = l1_scratchpad_addr[0];
                end
                8'h1c: begin //scratchpad address 1
                    rdata_d = l1_scratchpad_addr[1];
                end
                8'h20: begin //scratchpad address 2
                    rdata_d = l1_scratchpad_addr[2];
                end
                8'h24: begin //scratchpad address 3
                    rdata_d = l1_scratchpad_addr[3];
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
                    rdata_d[31:C_MSGID_WIDTH] = '0;
                    rdata_d[C_MSGID_WIDTH-1:0] = current_task_q.handler_task.msgid;
                end

                /* Handler termination */
                8'h50: begin //feedback flag (reading this address leads to the sending of the feedback)
                    rdata_d = 32'h00000000;
                    trigger_feedback = 1'b1;
                end

                /* Handler error */
                8'h54: begin
                    if (~wen_ni) begin
                        handler_error_code = wdata_i;
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
            pmp_cfg_q <= '0;
            pmp_addr_q <= '0;
        end else begin
            state_q <= state_d;
            current_task_q <= current_task_d;
            valid_q <= valid_d;
            rdata_q <= rdata_d;
            pmp_cfg_q <= pmp_cfg_d;
            pmp_addr_q <= pmp_addr_d;
        end
    end
    
    
    // pragma translate_off
    `ifndef VERILATOR
    initial begin
        static int handler_start_time = 0;
        static int timediff;
        /*
        forever begin
            @(posedge clk_i);
            if (hpu_task_valid_i && hpu_task_ready_o) begin
                $display("HPU (%0d, %0d) task (msg_id: %0d; pkt_addr: %0d; handler: %0d, scratchpad_id: %0d)!", cluster_id_i, C_CORE_ID, hpu_task_i.handler_task.msgid, hpu_task_i.handler_task.pkt_addr, hpu_task_i.handler_task.handler_fun, scratchpad_id);
            end
        end
         */
        forever begin            
            @(posedge clk_i);
            if (hpu_task_valid_i && hpu_task_ready_o) begin
                handler_start_time = $stime;
                $display("%0d INFO HANDLER_START %0d %0d", $stime, cluster_id_i, C_CORE_ID);
            end

            if (state_q != Init && state_q != Idle && state_d == Idle) begin
                timediff = $stime - handler_start_time;
                $display("%0d INFO HPU_TIME %0d %0d %0d", $stime, cluster_id_i, C_CORE_ID, timediff);                  
            end

            if (state_q == Running && trigger_feedback) begin
                timediff = $stime - handler_start_time;
                $display("%0d INFO HANDLER_TIME %0d %0d %0d %0d %0d %0d %0d", $stime, cluster_id_i, C_CORE_ID, current_task_q.handler_task.msgid, current_task_q.handler_task.handler_fun, timediff, current_task_q.handler_task.pkt_addr, current_task_q.handler_task.pkt_size);
                //$display("MSG: %0d; scratchpad id: %0d; scratchpad base addr: %0d; scratchpad size: %0d", current_task_q.handler_task.msgid, scratchpad_id, l1_scratchpad_base_addr, L1_SCRATCHPAD_SIZE);
            end

            if (handler_error) begin
                $display("%0d HPU (%0d %0d) HANDLER ERROR: %0d", $stime, cluster_id_i, C_CORE_ID, handler_error_code);
            end
        end
    end
    `else
        always_ff @(posedge clk_i, negedge rst_ni) begin
            if (hpu_task_valid_i && hpu_task_ready_o) begin
                $display("[%0d][synt]: INFO HANDLER_START %0d %0d", $stime, cluster_id_i, C_CORE_ID);
            end

            if (state_q != Init && state_q != Idle && state_d == Idle) begin
                $display("[%0d][synt]: INFO HPU_TIME %0d %0d", $stime, cluster_id_i, C_CORE_ID);                  
            end

            if (state_q == Running && trigger_feedback) begin
                $display("[%0d][synt]: INFO HANDLER_TIME %0d %0d %0d %08x %08x %0d", $stime, cluster_id_i, C_CORE_ID, current_task_q.handler_task.msgid, current_task_q.handler_task.handler_fun, current_task_q.handler_task.pkt_addr, current_task_q.handler_task.pkt_size);
                //$display("MSG: %0d; scratchpad id: %0d; scratchpad base addr: %0d; scratchpad size: %0d", current_task_q.handler_task.msgid, scratchpad_id, l1_scratchpad_base_addr, L1_SCRATCHPAD_SIZE);
            end

            if (handler_error) begin
                $display("[%0d][synt]: HPU (%0d %0d) HANDLER ERROR: %0d", $stime, cluster_id_i, C_CORE_ID, handler_error_code);
            end
        end
    `endif
    // pragma translate_on

endmodule

module cmd_frontend #(
    parameter int C_CORE_ID        = 0,
    parameter int NUM_CMDS         = 4,
    parameter int NUM_BUFFERED_CMD = 1
) (
    input logic                   clk_i,
    input logic                   rst_ni,

    input logic [5:0]             cluster_id_i,

    input  logic                  req_i,
    input  logic [31:0]           add_i,
    input  logic                  wen_ni,
    input  logic [31:0]           wdata_i,
    input  logic [3:0]            be_i,
    output logic                  gnt_o,
    output logic [31:0]           r_rdata_o,
    output logic                  r_valid_o,

    input  logic                  cmd_resp_valid_i,
    input  pspin_cmd_resp_t       cmd_resp_i,

    input  logic                  disabled_i,
    output logic                  no_pending_cmd_o,

    input  logic                  cmd_ready_i,
    output logic                  cmd_valid_o,
    output pspin_cmd_t            cmd_o
);
    
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
    pspin_cmd_t cmd_d, cmd_q;
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
        .dtype     (pspin_cmd_t),
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
    assign cmd_d.cmd_id.core_id = C_CORE_ID;

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
endmodule
