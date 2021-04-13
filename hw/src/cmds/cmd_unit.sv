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

module cmd_unit #(
    parameter int unsigned NUM_CLUSTERS             = 4,
    parameter int unsigned NUM_CMD_INTERFACES       = 2,
    parameter int unsigned INTF_RESP_BUFF_SIZE      = 8
) (
    input logic                                         clk_i,
    input logic                                         rst_ni,

    output logic [NUM_CLUSTERS-1:0]                     cmd_ready_o,
    input  logic [NUM_CLUSTERS-1:0]                     cmd_valid_i,
    input  pspin_cmd_t [NUM_CLUSTERS-1:0]               cmd_i,

    output logic                                        cmd_resp_valid_o,
    output pspin_cmd_resp_t                             cmd_resp_o,

    input  logic [NUM_CMD_INTERFACES-1:0]               intf_ready_i,
    output logic [NUM_CMD_INTERFACES-1:0]               intf_valid_o,
    output pspin_cmd_t [NUM_CMD_INTERFACES-1:0]         intf_cmd_o,

    input  logic [NUM_CMD_INTERFACES-1:0]               intf_cmd_resp_valid_i,
    input  pspin_cmd_resp_t [NUM_CMD_INTERFACES-1:0]    intf_cmd_resp_i
);

    /* spill registers from clusters */
    logic [NUM_CLUSTERS-1:0] cluster_cmd_ready;
    logic [NUM_CLUSTERS-1:0] cluster_cmd_valid;
    pspin_cmd_t [NUM_CLUSTERS-1:0] cluster_cmd;

    for (genvar i=0; i<NUM_CLUSTERS; i++) begin : gen_cluster_spill_reg
        spill_register #(
            .T       (pspin_cmd_t)
        ) i_cluster_cmd_spill (
            .clk_i   (clk_i),
            .rst_ni  (rst_ni),
            .valid_i (cmd_valid_i[i]),
            .ready_o (cmd_ready_o[i]),
            .data_i  (cmd_i[i]),
            .valid_o (cluster_cmd_valid[i]),
            .ready_i (cluster_cmd_ready[i]),
            .data_o  (cluster_cmd[i])
        );
    end

    /* stream demux */
    logic [NUM_CLUSTERS-1:0][NUM_CMD_INTERFACES-1:0] intf_demux_valid;
    logic [NUM_CLUSTERS-1:0][NUM_CMD_INTERFACES-1:0] intf_demux_ready;

    for (genvar i=0; i<NUM_CLUSTERS; i++) begin : gen_cluster_stream_demux
        stream_demux #(
            .N_OUP          (NUM_CMD_INTERFACES)
        ) i_stream_demux_cluster_cmd (
            .inp_valid_i    (cluster_cmd_valid[i]),
            .inp_ready_o    (cluster_cmd_ready[i]),
            .oup_sel_i      (cluster_cmd[i].intf_id),
            .oup_valid_o    (intf_demux_valid[i]),
            .oup_ready_i    (intf_demux_ready[i])
        );
    end

    /* cross wires */
    logic [NUM_CMD_INTERFACES-1:0][NUM_CLUSTERS-1:0] intf_mux_valid;
    logic [NUM_CMD_INTERFACES-1:0][NUM_CLUSTERS-1:0] intf_mux_ready;

    for (genvar i=0; i<NUM_CMD_INTERFACES; i++) begin: gen_xbar_l1
        for (genvar j=0; j<NUM_CLUSTERS; j++) begin: gen_xbar_l2
            assign intf_mux_valid[i][j] = intf_demux_valid[j][i];
            assign intf_demux_ready[j][i] = intf_mux_ready[i][j];
        end
    end

    /* round robin on interfaces */
    logic [NUM_CMD_INTERFACES-1:0] cmd_arb_ready;
    logic [NUM_CMD_INTERFACES-1:0] cmd_arb_valid;
    pspin_cmd_t [NUM_CMD_INTERFACES-1:0] cmd_arb_cmd;

    logic [NUM_CMD_INTERFACES-1:0] fifo_in_flight_req_has_space;

    for (genvar i=0; i<NUM_CMD_INTERFACES; i++) begin: gen_rr_arb
        // select a cluster to serve
        rr_arb_tree #(
            .NumIn      (NUM_CLUSTERS),
            .DataType   (pspin_cmd_t),
            .ExtPrio    (0),
            .AxiVldRdy  (1),
            .LockIn     (1)
        ) i_cmd_intf_arb (
            .clk_i      (clk_i),
            .rst_ni     (rst_ni),
            .flush_i    (1'b0),
            .rr_i       ('0),
            .req_i      (intf_mux_valid[i]),
            .gnt_o      (intf_mux_ready[i]),
            .data_i     (cluster_cmd),
            .gnt_i      (cmd_arb_ready[i]),
            .req_o      (cmd_arb_valid[i]),
            .data_o     (cmd_arb_cmd[i]),
            .idx_o      ()
        );

        assign intf_valid_o[i]  = cmd_arb_valid[i] && fifo_in_flight_req_has_space[i];
        assign cmd_arb_ready[i] = intf_ready_i[i] && fifo_in_flight_req_has_space[i];
        assign intf_cmd_o[i]    = cmd_arb_cmd[i];
    end

    /* in flight requests fifo & response buffer */
    logic [NUM_CMD_INTERFACES-1:0] fifo_in_flight_req_pop;
    logic [NUM_CMD_INTERFACES-1:0] fifo_in_flight_req_push;
    logic [NUM_CMD_INTERFACES-1:0][$clog2(INTF_RESP_BUFF_SIZE)-1:0] fifo_in_flight_req_usage;
    logic [NUM_CMD_INTERFACES-1:0] fifo_resp_buffer_pop;
    logic [NUM_CMD_INTERFACES-1:0] fifo_resp_buffer_push;
    logic [NUM_CMD_INTERFACES-1:0] fifo_resp_buffer_empty;
    logic [NUM_CMD_INTERFACES-1:0] fifo_resp_buffer_valid;
    logic [NUM_CMD_INTERFACES-1:0] fifo_resp_buffer_ready;

    pspin_cmd_resp_t [NUM_CMD_INTERFACES-1:0] fifo_resp_buffer_data;

    pspin_cmd_resp_t resp_arb_data;
    logic resp_arb_valid;

    for (genvar i=0; i<NUM_CMD_INTERFACES; i++) begin: gen_fifo_req
        fifo_v3 #(
            .dtype     (logic),
            .DEPTH     (INTF_RESP_BUFF_SIZE)
        ) i_req_fifo (
            .clk_i     (clk_i),
            .rst_ni    (rst_ni),
            .flush_i   (1'b0),
            .testmode_i(1'b0),
            .full_o    (),
            .empty_o   (),
            .usage_o   (fifo_in_flight_req_usage[i]),
            .data_i    (1'b1),
            .push_i    (fifo_in_flight_req_push[i]),
            .data_o    (),
            .pop_i     (fifo_in_flight_req_pop[i])
        ); 

        assign fifo_in_flight_req_push[i]       = cmd_arb_valid[i] && cmd_arb_ready[i];
        assign fifo_in_flight_req_pop[i]        = fifo_resp_buffer_pop[i];
        assign fifo_in_flight_req_has_space[i]  = fifo_in_flight_req_usage[i] < INTF_RESP_BUFF_SIZE - 1;
    end

    for (genvar i=0; i<NUM_CMD_INTERFACES; i++) begin: gen_fifo_resp
        fifo_v3 #(
            .dtype     (pspin_cmd_resp_t),
            .DEPTH     (INTF_RESP_BUFF_SIZE)
        ) i_resp_fifo (
            .clk_i     (clk_i),
            .rst_ni    (rst_ni),
            .flush_i   (1'b0),
            .testmode_i(1'b0),
            .full_o    (),
            .empty_o   (fifo_resp_buffer_empty[i]),
            .usage_o   (),
            .data_i    (intf_cmd_resp_i[i]),
            .push_i    (fifo_resp_buffer_push[i]),
            .data_o    (fifo_resp_buffer_data[i]),
            .pop_i     (fifo_resp_buffer_pop[i])
        ); 

        assign fifo_resp_buffer_push[i] = intf_cmd_resp_valid_i[i];
        assign fifo_resp_buffer_pop[i] = fifo_resp_buffer_ready[i] && fifo_resp_buffer_valid[i];
        assign fifo_resp_buffer_valid[i] = !fifo_resp_buffer_empty[i];
    end

    rr_arb_tree #(
        .NumIn      (NUM_CMD_INTERFACES),
        .DataType   (pspin_cmd_resp_t),
        .ExtPrio    (0),
        .AxiVldRdy  (1),
        .LockIn     (1)
    ) i_cmd_resp_arb (
        .clk_i      (clk_i),
        .rst_ni     (rst_ni),
        .flush_i    (1'b0),
        .rr_i       ('0),
        .req_i      (fifo_resp_buffer_valid),
        .gnt_o      (fifo_resp_buffer_ready),
        .data_i     (fifo_resp_buffer_data),
        .gnt_i      (1'b1),
        .req_o      (resp_arb_valid),
        .data_o     (resp_arb_data),
        .idx_o      ()
    );

    /* spill register to clusters */
    spill_register #(
        .T(pspin_cmd_resp_t)
    ) i_cluster_cmd_resp_spill (
        .clk_i   (clk_i),
        .rst_ni  (rst_ni),
        .valid_i (resp_arb_valid),
        .ready_o (),
        .data_i  (resp_arb_data),
        .valid_o (cmd_resp_valid_o),
        .ready_i (1'b1),
        .data_o  (cmd_resp_o)    
    );

endmodule
