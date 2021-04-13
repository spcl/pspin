// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// TODO: Replace behavior with instantiation of cuts.

module sram #(
  parameter int unsigned DATA_WIDTH = 0,   // [bit]
  parameter int unsigned N_WORDS    = 0,
  parameter              SimInit    = "none",  
  // Dependent parameters, do not override!
  parameter int unsigned N_BYTES = DATA_WIDTH/8,
  parameter type addr_t = logic[$clog2(N_WORDS)-1:0],
  parameter type data_t = logic[DATA_WIDTH-1:0],
  parameter type strb_t = logic[N_BYTES-1:0]
) (
  input  logic  clk_i,
  input  logic  rst_ni,
  input  logic  req_i,
  input  logic  we_i,
  input  addr_t addr_i,
  input  data_t wdata_i,
  input  strb_t be_i,
  output data_t rdata_o
);

  tc_sram #(
    .NumWords     ( N_WORDS     ),
    .DataWidth    ( DATA_WIDTH  ),
    .ByteWidth    ( 8           ),
    .NumPorts     ( 1           ),
    .Latency      ( 1           ),
    .SimInit      ( SimInit     ),
    .PrintSimCfg  ( 1'b0        )
  ) i_tc_sram (
    .clk_i,
    .rst_ni,
    .req_i,
    .we_i,
    .addr_i,
    .wdata_i,
    .be_i,
    .rdata_o
  );

endmodule
