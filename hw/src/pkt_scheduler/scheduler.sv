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

/** 
 NOTE: this module needs to be revisioned because by introducing a packet buffer in L1 we don't have
 the concept of "packet slots" anymore. The cluster_occup_i signal should be signal the available space
 instead of the number of available packet slots. 
**/

module scheduler #(
    parameter int NUM_CLUSTERS          = 4,
    parameter int NUM_HERS_PER_CLUSTER  = 64
) (
    input   logic                               clk_i,
    input   logic                               rst_ni,

    //input IF from MPQ engine
    input   logic                               task_valid_i,
    output  logic                               task_ready_o,
    input   handler_task_t                      task_descr_i,

    //output IF to cluster schedulers
    output logic [NUM_CLUSTERS-1:0]             cluster_task_valid_o,
    input  logic [NUM_CLUSTERS-1:0]             cluster_task_ready_i,
    output handler_task_t [NUM_CLUSTERS-1:0]    cluster_task_descr_o,

    //input IF from clusters for the feedbacks
    input  logic [NUM_CLUSTERS-1:0]             cluster_feedback_valid_i,
    output logic [NUM_CLUSTERS-1:0]             cluster_feedback_ready_o,
    input  feedback_descr_t [NUM_CLUSTERS-1:0]  cluster_feedback_i,

    //output IF to pktgen for feedbacks
    output logic                                pktgen_feedback_valid_o,
    input  logic                                pktgen_feedback_ready_i,
    output feedback_descr_t                     pktgen_feedback_o 
    
);

    /////////////////////////
    /// Cluster interface ///
    /////////////////////////

    // We use these registers to cut the combinatorial network from 
    // the uncluster (outside a cluster) to inside a cluster. This helps
    // defining domains and to close timings separately. It also reduces
    // paths lengths. 
    logic [NUM_CLUSTERS-1:0]             cluster_task_valid_od;
    logic [NUM_CLUSTERS-1:0]             cluster_task_ready_id;
    handler_task_t [NUM_CLUSTERS-1:0]    cluster_task_descr_od;

    logic [NUM_CLUSTERS-1:0]             cluster_feedback_valid_iq;
    logic [NUM_CLUSTERS-1:0]             cluster_feedback_ready_oq;
    feedback_descr_t [NUM_CLUSTERS-1:0]  cluster_feedback_iq;

    for (genvar i=0; i<NUM_CLUSTERS; i++) begin
        spill_register #(
            .T       (handler_task_t)
        ) i_cluster_task_spill (
            .clk_i   (clk_i),
            .rst_ni  (rst_ni),
            .valid_i (cluster_task_valid_od[i]),
            .ready_o (cluster_task_ready_id[i]),
            .data_i  (cluster_task_descr_od[i]),
            .valid_o (cluster_task_valid_o[i]),
            .ready_i (cluster_task_ready_i[i]),
            .data_o  (cluster_task_descr_o[i])
        );

        spill_register #(
            .T       (feedback_descr_t)
        ) i_cluster_feedback_spill (
            .clk_i   (clk_i),
            .rst_ni  (rst_ni),
            .valid_i (cluster_feedback_valid_i[i]),
            .ready_o (cluster_feedback_ready_o[i]),
            .data_i  (cluster_feedback_i[i]),
            .valid_o (cluster_feedback_valid_iq[i]),
            .ready_i (cluster_feedback_ready_oq[i]),
            .data_o  (cluster_feedback_iq[i])
        );
    end

    /////////////////////////////////////////////
    /// Scheduling HERs to cluster schedulers ///
    /////////////////////////////////////////////

    localparam int MAX_OCC = (NUM_HERS_PER_CLUSTER);

    /** State **/
    // current state
    typedef enum logic {ServePacket, WaitTransfer} state_t;
    state_t     state_d, state_q;

    logic [NUM_CLUSTERS-1:0][$clog2(NUM_HERS_PER_CLUSTER):0] cluster_occup_q;
    logic [NUM_CLUSTERS-1:0][$clog2(NUM_HERS_PER_CLUSTER):0] cluster_occup_d;

    // set if we are pushing a request to a cluster (e.g., waiting for the ready signal)
    logic serving_cluster;

    // currently selected cluster (used to remember the cluster ID if we are waiting for the ready signal)
    logic [$clog2(NUM_CLUSTERS)-1:0] cluster_id_d;
    logic [$clog2(NUM_CLUSTERS)-1:0] cluster_id_q;
    logic [$clog2(NUM_CLUSTERS)-1:0] sel_cluster_id;

    handler_task_t task_q, task_d;
    /** end state **/

    /** combinatorial part **/

    assign task_d = (task_valid_i && task_ready_o) ? task_descr_i : task_q;

    // update cluster occupation (both packets and space)
    for (genvar i=0; i<NUM_CLUSTERS; i++) begin: gen_cluster_occup

        always_comb begin
            case ({cluster_task_valid_od[i] & cluster_task_ready_id[i], cluster_feedback_valid_iq[i] & cluster_feedback_ready_oq[i]})
                2'b10   : cluster_occup_d[i] = cluster_occup_q[i] + 1;
                2'b01   : cluster_occup_d[i] = cluster_occup_q[i] - 1;
                default : cluster_occup_d[i] = cluster_occup_q[i];
            endcase   
        end
    end

    //home cluster is in the last clog(NUM_CLUSTERS) bits of msg_id
    logic [$clog2(NUM_CLUSTERS)-1:0] home_cluster_id;
    assign home_cluster_id[$clog2(NUM_CLUSTERS)-1:0] = task_descr_i.msgid[$clog2(NUM_CLUSTERS)-1:0];

    logic no_cluster_avail;
    logic can_use_home_cluster;
    logic [$clog2(NUM_CLUSTERS)-1:0] c_occup_min;

    //cluster_id is home_cluster if there is space in it, otherwise is the least loaded cluster
    //if no cluster are available, no_cluster_avail_d is 1
    
    //if there is not cluster avail, then we schedule to the home cluster anyway.. we don't have additional info to make a better decision.
    //Otherwise, we schedule to the home cluster if it has space (<MAX OCC) and it is ready to accept the new packets (there may be fragmentation in the cluster, 
    //there might not space even if the occupation is ok).
    assign no_cluster_avail     = (cluster_occup_q[c_occup_min] >= MAX_OCC) ? 1'b1 : 1'b0;    
    assign can_use_home_cluster = (no_cluster_avail || (cluster_occup_q[home_cluster_id] < MAX_OCC && cluster_task_ready_id[home_cluster_id]));
    assign sel_cluster_id       = (can_use_home_cluster) ? home_cluster_id : c_occup_min;
    assign cluster_id_d         = (state_q == ServePacket) ? sel_cluster_id : cluster_id_q;

    //task is put on all the output interfaces. Only the selected cluster ID will have
    //cluster_valid_o[i] set. 
    for (genvar i = 0; i < NUM_CLUSTERS; i++) begin : gen_cluster_task
        assign cluster_task_descr_od[i] = (state_q == ServePacket) ? task_descr_i : task_q;
        assign cluster_task_valid_od[i] = (cluster_id_d == i) && serving_cluster;
    end

    always_comb begin
        int i;
        state_d = state_q;
        task_ready_o = 1'b0;
        serving_cluster = 1'b0;

        case (state_q)
            ServePacket: begin
                serving_cluster = 1'b0;

                if (task_valid_i && !no_cluster_avail) begin
                    task_ready_o = 1'b1; //signal that we recvd the data
                    state_d = (cluster_task_ready_id[cluster_id_d]) ? ServePacket : WaitTransfer;
                    serving_cluster = 1'b1;
                end
            end
            WaitTransfer: begin
                serving_cluster = 1'b1;
                if ((cluster_task_ready_id[cluster_id_q])) begin
                   state_d = ServePacket;
                end
            end
            default: begin
                state_d = ServePacket;
            end

        endcase
    end

    argmin4 #(
        .VALUE_WIDTH    ($clog2(NUM_HERS_PER_CLUSTER)+1)
    ) i_argmin4 (
        .values_i(cluster_occup_q),
        .enabled_i(cluster_task_ready_id),
        .argmin_o(c_occup_min)
    );  

    /** sequential part **/
    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin   
            state_q <= ServePacket;
            cluster_id_q <= '0;
            task_q <= '0;
            cluster_occup_q <= '0;
        end else begin
            state_q <= state_d;
            cluster_id_q <= cluster_id_d;
            task_q <= task_d;
            cluster_occup_q <= cluster_occup_d;
        end
    end

    /** simulation **/
    /*
    initial begin
        forever begin
            @(posedge clk_i);
            if (task_valid_i && task_ready_o) begin
                $display("[sched] msg_id: %0d; cluster_id: %0d; occupation: %0d; no_cluster_avail: %0d", task_descr_i.msgid, cluster_id_d, cluster_occup_iq[cluster_id_d], no_cluster_avail);
            end
        end
    end
    */

    // pragma translate_off
    `ifndef VERILATOR
    initial begin
        static int start_time = 0;
        forever begin
            @(posedge clk_i);
            if (task_valid_i && task_ready_o && start_time == 0) begin
                start_time = $stime;
            end

            if (task_valid_i && task_ready_o) begin
                $display("%0d INFO TASK %0d %0d", $stime, task_descr_i.msgid, ($stime - start_time));
            end

            if (pktgen_feedback_valid_o && pktgen_feedback_ready_i) begin
                $display("%0d INFO FEEDBACK %0d %0d", $stime, pktgen_feedback_o.msgid, ($stime - start_time));
            end
        end
    end
    `endif
    // pragma translate_on

    /////////////////////////////////////////////////////
    /// Arbitrating feedbacks from cluster schedulers ///
    /////////////////////////////////////////////////////

    //logic [$clog2(NUM_CLUSTERS)-1:0] cluster_idx_arb;
    rr_arb_tree #(
        .NumIn      (NUM_CLUSTERS),
        .DataType   (feedback_descr_t),
        .ExtPrio    (0),
        .AxiVldRdy  (1),
        .LockIn     (1)
    ) i_rr_arb_tree (
        .clk_i      (clk_i),
        .rst_ni     (rst_ni),
        .flush_i    (1'b0),
        .rr_i       ('0),
        .req_i      (cluster_feedback_valid_iq),
        .gnt_o      (cluster_feedback_ready_oq),
        .data_i     (cluster_feedback_iq),
        .gnt_i      (pktgen_feedback_ready_i),
        .req_o      (pktgen_feedback_valid_o),
        .data_o     (pktgen_feedback_o),
        .idx_o      ()
    );

endmodule 

module argmin4 #(
    VALUE_WIDTH = 64
)
(
    input logic  [3:0][VALUE_WIDTH-1:0]     values_i,
    input logic  [3:0]                      enabled_i,
    output logic [1:0]                      argmin_o
);
    logic [1:0] min_l0;
    logic [1:0] min_l1;

    logic [3:0][VALUE_WIDTH-1:0] values;

    assign values[0] = (enabled_i[0]) ? values_i[0] : {VALUE_WIDTH{1'b1}};
    assign values[1] = (enabled_i[1]) ? values_i[1] : {VALUE_WIDTH{1'b1}};
    assign values[2] = (enabled_i[2]) ? values_i[2] : {VALUE_WIDTH{1'b1}};
    assign values[3] = (enabled_i[3]) ? values_i[3] : {VALUE_WIDTH{1'b1}};

    assign min_l0[1:0]   = (values[0] <= values[1]) ? 2'b00 : 2'b01;
    assign min_l1[1:0]   = (values[2] <= values[3]) ? 2'b10 : 2'b11;
    assign argmin_o[1:0] = (values[min_l0] <= values[min_l1]) ? min_l0 : min_l1;
endmodule