// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Thomas Benz <tbenz@ethz.ch>

// transaction id generator. just increase the transaction id on every request

module transfer_id_gen #(
    parameter int unsigned  ID_WIDTH  = -1
) (
    input  logic                clk_i,
    input  logic                rst_ni,
    // new request is pushed
    input  logic                issue_i,
    // request is popped
    input  logic                retire_i,
    // next id is
    output logic [ID_WIDTH-1:0] next_o,
    // last id completed is
    output logic [ID_WIDTH-1:0] completed_o
);

    //--------------------------------------
    // counters
    //-------------------------------------- 
    logic [ID_WIDTH-1:0] next_d,      next_q;
    logic [ID_WIDTH-1:0] completed_d, completed_q;

    // count up on events
    assign next_d      = (issue_i  == 1'b1) ? next_q + 'h1      : next_q;
    assign completed_d = (retire_i == 1'b1) ? completed_q + 'h1 : completed_q;

    // assign outputs
    assign next_o      = next_q;
    assign completed_o = completed_q;

    //--------------------------------------
    // state
    //-------------------------------------- 
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_id_gen
        if(~rst_ni) begin
            next_q      <=  1;
            completed_q <= 0;
        end else begin
            next_q      <= next_d;
            completed_q <= completed_d;
        end
    end

endmodule : transfer_id_gen

