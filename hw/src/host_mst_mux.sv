// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


`include "axi/typedef.svh"

module host_mst_mux #(
  parameter int unsigned AddrWidth = 0,
  parameter int unsigned DataWidth = 0,
  parameter int unsigned IdWidth = 0,
  parameter int unsigned UserWidth = 0,
  parameter type req_t = logic,
  parameter type resp_t = logic,
  // Dependent parameters, DO NOT OVERRIDE!
  parameter type addr_t = logic [AddrWidth-1:0]
) (
  input  logic  clk_i,
  input  logic  rst_ni,

  input  req_t dma_req_i,
  output resp_t dma_resp_o,

  input  req_t hdir_req_i,
  output resp_t hdir_resp_o,

  output req_t host_req_o,
  input  resp_t host_resp_i
);

  localparam int unsigned NoSlavePorts = 2;
  localparam int unsigned MuxIdWidth = IdWidth + cf_math_pkg::idx_width(NoSlavePorts);


  // Types of input and output channels.
  typedef logic [DataWidth-1:0]   data_t;
  typedef logic [DataWidth/8-1:0] strb_t;
  typedef logic [IdWidth-1:0]     id_t;
  typedef logic [UserWidth-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_t, data_t, id_t, user_t)


  typedef logic [MuxIdWidth-1:0] mux_id_t;
  `AXI_TYPEDEF_AW_CHAN_T(mux_aw_t, addr_t, mux_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mux_b_t, mux_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mux_ar_t, addr_t, mux_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mux_r_t, data_t, mux_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(mux_req_t, mux_aw_t, w_t, mux_ar_t)
  `AXI_TYPEDEF_RESP_T(mux_resp_t, mux_b_t, mux_r_t)

  mux_req_t mux_req;
  mux_resp_t mux_resp;

  axi_mux #(
    .SlvAxiIDWidth      (IdWidth),
    .slv_aw_chan_t      (aw_t),
    .mst_aw_chan_t      (mux_aw_t),
    .w_chan_t           (w_t),
    .slv_b_chan_t       (b_t),
    .mst_b_chan_t       (mux_b_t),
    .slv_ar_chan_t      (ar_t),
    .mst_ar_chan_t      (mux_ar_t),
    .slv_r_chan_t       (r_t),
    .mst_r_chan_t       (mux_r_t),
    .slv_req_t          (req_t),
    .slv_resp_t         (resp_t),
    .mst_req_t          (mux_req_t),
    .mst_resp_t         (mux_resp_t),
    .NoSlvPorts         (NoSlavePorts)
  ) i_mux_host_mst (
    .clk_i              (clk_i),
    .rst_ni             (rst_ni),
    .test_i             (1'b0),
    .slv_reqs_i         ({dma_req_i,   hdir_req_i}),
    .slv_resps_o        ({dma_resp_o,  hdir_resp_o}),
    .mst_req_o          (mux_req),
    .mst_resp_i         (mux_resp)
  );

  axi_id_remap #(
    .AxiSlvPortIdWidth    (MuxIdWidth),
    .AxiMstPortIdWidth    (IdWidth),
    .AxiSlvPortMaxUniqIds (8),  // TODO: calibrate
    .AxiMaxTxnsPerId      (2),  // TODO: calibrate (=depth of store buffer?)
    .slv_req_t            (mux_req_t),
    .slv_resp_t           (mux_resp_t),
    .mst_req_t            (req_t),
    .mst_resp_t           (resp_t)
  ) i_hnd_iw_converter (
    .clk_i,
    .rst_ni,
    .slv_req_i  (mux_req),
    .slv_resp_o (mux_resp),
    .mst_req_o  (host_req_o),
    .mst_resp_i (host_resp_i)
  );

endmodule
