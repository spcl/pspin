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

module cluster_cmd #(
    parameter int unsigned NUM_CORES = 8
) (
    input  logic                        clk_i,
    input  logic                        rst_ni,

    //from hpu drivers (commands)
    output logic [NUM_CORES-1:0]        cmd_ready_o,
    input  logic [NUM_CORES-1:0]        cmd_valid_i,
    input  pspin_cmd_t [NUM_CORES-1:0]  cmd_i,

    //to uncluster 
    input  logic                        cmd_ready_i,
    output logic                        cmd_valid_o,
    output pspin_cmd_t                  cmd_o 
);

    rr_arb_tree #(
        .NumIn      (NUM_CORES),
        .DataType   (pspin_cmd_t),
        .ExtPrio    (0),
        .AxiVldRdy  (1),
        .LockIn     (1)
    ) i_cluster_cmd_arb (
        .clk_i      (clk_i),
        .rst_ni     (rst_ni),
        .flush_i    (1'b0),
        .rr_i       ('0),
        .req_i      (cmd_valid_i),
        .gnt_o      (cmd_ready_o),
        .data_i     (cmd_i),
        .gnt_i      (cmd_ready_i),
        .req_o      (cmd_valid_o),
        .data_o     (cmd_o),
        .idx_o      ()
    );

endmodule
