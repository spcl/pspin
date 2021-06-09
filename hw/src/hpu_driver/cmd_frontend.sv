// Copyright (c) 2021 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module cmd_frontend #(
    parameter int unsigned NUM_CMDS         = 4,
    parameter int unsigned NUM_BUFFERED_CMD = 1,
    parameter int unsigned CLUSTER_ID_WIDTH = 16,
    parameter int unsigned CORE_ID_WIDTH    = 16,
    parameter int unsigned DATA_WIDTH       = 64,
    parameter type cmd_req_t                = logic,
    parameter type cmd_resp_t               = logic,
    parameter type dreq_t                   = logic,
    parameter type drsp_t                   = logic,
    parameter type drsp_chan_t              = logic
) (
    input logic                        clk_i,
    input logic                        rst_ni,

    input logic [CLUSTER_ID_WIDTH-1:0] cluster_id_i,
    input logic [CORE_ID_WIDTH-1:0]    core_id_i,

    input  dreq_t                      core_req_i,
    output drsp_t                      core_resp_o,

    input  logic                       cmd_resp_valid_i,
    input  cmd_resp_t                  cmd_resp_i,

    input  logic                       disable_commands_i,
    input  logic                       release_all_commands_i,
    output logic                       no_pending_cmd_o,

    input  logic                       cmd_ready_i,
    output logic                       cmd_valid_o,
    output cmd_req_t                   cmd_o
);
    localparam int unsigned ID_WIDTH = cf_math_pkg::idx_width(NUM_CMDS);
    localparam int unsigned DataAlign = $clog2(DATA_WIDTH/8);

    typedef enum logic [1:0] {Disabled, Ready, Stalled, Waiting} state_t;
    state_t state_d, state_q;

    logic new_cmd_req_fifo_ready, new_cmd_req_fifo_valid;
    logic next_id_valid, next_id_pop;
    logic [ID_WIDTH-1:0] next_id;
    logic [ID_WIDTH-1:0] last_cmd_id_d, last_cmd_id_q;
    logic issue_cmd, issue_wait, write_test_id, can_issue_cmd;
    logic release_id;
    
    logic [DataAlign-1:0] core_req_i_data_offset;
    logic [31:0] core_req_i_data_shifted;

    cmd_req_t new_cmd_req_d, new_cmd_req_q;

    // IDs that can be used
    logic [NUM_CMDS-1:0] free_cmd_ids;

    // IDs that have been released by the core
    logic [NUM_CMDS-1:0] released_cmd_ids_d, released_cmd_ids_q;

    // IDs that have been completed
    logic [NUM_CMDS-1:0] completed_cmd_ids_d, completed_cmd_ids_q;

    logic no_free_cmd_ids;

    logic [$clog2(NUM_CMDS)-1:0] wt_cmd_idx, wt_cmd_idx_d, wt_cmd_idx_q;
    logic wt_cmd_finished;

    logic [4:0] add_idx;
    
    logic core_resp_ready, core_resp_valid;
    drsp_chan_t core_resp;

    // Next ID to use
    lzc #(
        .WIDTH  (NUM_CMDS)
    ) i_lzc_free_cmd_ids (
        .in_i    (free_cmd_ids),
        .cnt_o   (next_id),
        .empty_o (no_free_cmd_ids)
    );

    stream_fifo #(
        .FALL_THROUGH   (1'b0),
        .DEPTH          (NUM_BUFFERED_CMD),
        .T              (cmd_req_t)
    ) i_cmd_fifo (
        .clk_i      ( clk_i                  ),      
        .rst_ni     ( rst_ni                 ),     
        .flush_i    ( 1'b0                   ),    
        .testmode_i ( 1'b0                   ), 
        .usage_o    ( /*unconnected*/        ),    
        .data_i     ( new_cmd_req_q          ),
        .valid_i    ( new_cmd_req_fifo_valid ),
        .ready_o    ( new_cmd_req_fifo_ready ),
        .data_o     ( cmd_o                  ), 
        .valid_o    ( cmd_valid_o            ),
        .ready_i    ( cmd_ready_i            ) 
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

    // Shift input data
    assign core_req_i_data_offset = core_req_i.q.addr[DataAlign-1:0];
    assign core_req_i_data_shifted = core_req_i.q.data >> {core_req_i_data_offset, 3'b000};

    // the next ID is valid if there free cmds
    assign next_id_valid = ~no_free_cmd_ids;

    // free IDs are IDs that have been released and completed
    assign free_cmd_ids = released_cmd_ids_q & completed_cmd_ids_q;

    // we can issue a new cmd only if we have buffer space (if there are no IDs we just return error)
    assign can_issue_cmd = new_cmd_req_fifo_ready;

    // address idx, identifies a command issued by the core
    assign add_idx = core_req_i.q.addr[6:2];

    // wait/test cmd id
    assign wt_cmd_idx = core_req_i_data_shifted[$clog2(NUM_CMDS)-1:0];
    assign wt_cmd_idx_d = (write_test_id) ? wt_cmd_idx : wt_cmd_idx_q;
    assign wt_cmd_finished = (completed_cmd_ids_q[wt_cmd_idx_d] == 1'b1) || (cmd_resp_valid_i && cmd_resp_i.cmd_id.local_cmd_id == wt_cmd_idx_d);

    // no pending commands
    assign no_pending_cmd_o = (~free_cmd_ids == '0);

    // command ID
    assign new_cmd_req_d.cmd_id.cluster_id      = cluster_id_i;
    assign new_cmd_req_d.cmd_id.core_id         = core_id_i;
    assign new_cmd_req_d.cmd_id.local_cmd_id    = next_id;

    //state transitions
    always_comb begin
        state_d = state_q;

        case (state_q) 
            Ready: begin
                if (disable_commands_i) begin
                    state_d = Disabled;
                end
                else if (issue_cmd && !can_issue_cmd)  begin
                    state_d = Stalled;
                end
                else if (issue_wait && !wt_cmd_finished) begin
                    state_d = Waiting; 
                end                
            end

            Disabled: begin
                if (!disable_commands_i) begin
                    state_d = Ready;
                end
            end

            Stalled: begin
                if (can_issue_cmd) begin
                    state_d = Ready;
                end
            end

            Waiting: begin
                if (completed_cmd_ids_d[wt_cmd_idx_q] == 1'b1) begin
                    state_d = Ready;
                end
            end

        endcase
    end

    // issue cmd
    always_comb begin
        new_cmd_req_fifo_valid = 1'b0;
        next_id_pop = 1'b0;
        last_cmd_id_d = last_cmd_id_q;

        if (issue_cmd && can_issue_cmd && next_id_valid) begin
            new_cmd_req_fifo_valid = 1'b1;
            next_id_pop = 1'b1;
            last_cmd_id_d = next_id;         
        end
    end

    // handling core commands and responses
    assign core_resp_o.q_ready = (state_q == Ready && core_resp_ready);

    always_comb begin 
        core_resp.data = '0;
        core_resp_valid = 1'b0;
        issue_cmd = 1'b0;
        write_test_id = 1'b0;
        issue_wait = 1'b0;
        release_id = 1'b0;
        new_cmd_req_d.descr = new_cmd_req_q.descr;
        new_cmd_req_d.cmd_type = new_cmd_req_q.cmd_type;
        new_cmd_req_d.intf_id = new_cmd_req_q.intf_id;
        core_resp.error = 1'b0;

        case (state_q) 
            Ready: begin
                if (core_req_i.q_valid && !core_req_i.q.write) begin
                    if (add_idx == 0) begin /* ISSUE COMMAND */
                        core_resp.data[0] = ~next_id_valid;

                        // we reply only if 
                        // - we cannot serve the cmd rn because we don't have IDs OR
                        // - we are able to serve it right away (can_issue_cmd). Note that if this is not the case,
                        //   we delay the response to when we have space. We cannot do the same with the IDs because
                        //   there might be IDs that need to be released by the core before being reused. 
                        core_resp_valid = ~next_id_valid || can_issue_cmd;

                        // here we try to issue the cmd
                        issue_cmd = next_id_valid;
                    end
                    else if (add_idx == 1) begin /* READ LAST CMD ID */
                        core_resp.data[0] = last_cmd_id_q;
                        core_resp_valid = 1'b1;
                    end
                    else if (add_idx == 2) begin /* TEST CMD ID (reading test result) */
                        // we use completed_cmd_ids_d so to catch just arrived cmd responses
                        // we use wt_cmd_idx_q because the ID has been writtien here at least one cycle earlier (by the store)
                        core_resp.data = (completed_cmd_ids_d[wt_cmd_idx_q] == 1'b0) ? 32'h0000_0000 : 32'h0000_0001; 
                        core_resp_valid = 1'b1;
                        release_id = completed_cmd_ids_d[wt_cmd_idx_q];
                    end
                    else if (add_idx == 3) begin /* WAIT CMD ID */
                        issue_wait = 1'b1;
                        if (wt_cmd_finished) begin
                            core_resp_valid = 1'b1;
                            release_id = 1'b1;
                        end
                    end
                    else begin
                        core_resp.error = 1'b1;
                        core_resp_valid = 1'b1;
                    end
                end
                else if (core_req_i.q_valid && core_req_i.q.write) begin
                    if (add_idx == 2) begin /* WRITE CMD ID TO TEST/WAIT */
                        write_test_id = 1'b1;
                        core_resp_valid = 1'b1;
                    end
                    else if (add_idx == 4) begin /* CMD HEADER */ 
                        // FORMAT:
                        //   - 31:15 (16 bit): command type
                        //   - 14:14 (1 bit):  command targets an off-cluster command unit
                        //   - 13:0  (15 bit): interface ID
                        new_cmd_req_d.cmd_type = core_req_i_data_shifted[31:15];
                        new_cmd_req_d.to_uncluster = ~core_req_i_data_shifted[14];
                        new_cmd_req_d.intf_id = core_req_i_data_shifted[13:0];
                        core_resp_valid = 1'b1;
                    end
                    else if (add_idx >= 5 && add_idx <= 11) begin  /* CMD DESCRIPTOR */
                        new_cmd_req_d.descr.words[add_idx - 5] = core_req_i_data_shifted; 
                        core_resp_valid = 1'b1;
                    end
                    else begin
                        core_resp.error = 1'b1;
                        core_resp_valid = 1'b1;
                    end
                end
            end

            Stalled: begin
                // A buffer is now ready and we were waiting for it
                if (state_d == Ready) begin
                    core_resp.data[0] = '0;
                    core_resp_valid = 1'b1;
                    issue_cmd = 1'b1;
                end
            end

            Waiting: begin
                // The core was waiting for a command that now terminated
                if (state_d == Ready) begin
                    core_resp_valid = 1'b1;
                    release_id = 1'b1;
                end
            end
        endcase
    end

    // release IDs
    always_comb begin 
        released_cmd_ids_d = released_cmd_ids_q;

        if (release_id) begin
            released_cmd_ids_d[wt_cmd_idx_d] = 1'b1;
        end

        if (release_all_commands_i) begin
            released_cmd_ids_d = {NUM_CMDS{1'b1}};
        end

        if (issue_cmd && can_issue_cmd) begin
            released_cmd_ids_d[next_id] = 1'b0;
        end
    end

    // complete IDs
    always_comb begin
        completed_cmd_ids_d = completed_cmd_ids_q;

        if (cmd_resp_valid_i) begin
            completed_cmd_ids_d[cmd_resp_i.cmd_id.local_cmd_id] = 1'b1;
        end 

        if (issue_cmd && can_issue_cmd) begin
            completed_cmd_ids_d[next_id] = 1'b0;
        end
    end

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
            new_cmd_req_q <= '0; 
            last_cmd_id_q <= '0;
            state_q <= Ready;
            released_cmd_ids_q <= {NUM_CMDS{1'b1}};
            completed_cmd_ids_q <= {NUM_CMDS{1'b1}};
            wt_cmd_idx_q <= '0;
        end else begin
            new_cmd_req_q <= new_cmd_req_d;
            last_cmd_id_q <= last_cmd_id_d;
            state_q <= state_d;
            released_cmd_ids_q <= released_cmd_ids_d;
            completed_cmd_ids_q <= completed_cmd_ids_d;
            wt_cmd_idx_q <= wt_cmd_idx_d;
        end
    end

endmodule
