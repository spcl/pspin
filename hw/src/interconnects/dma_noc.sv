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

/// On-chip network interconnecting the DMA engines of all clusters to the L2.
module dma_noc #(
  parameter int unsigned NumClusters = 0,
  parameter int unsigned AddrWidth = 0,
  parameter int unsigned DataWidth = 0,
  parameter int unsigned DMAIdWidth = 0,
  parameter int unsigned L2IdWidth = 0,
  parameter int unsigned UserWidth = 0,
  parameter type dma_req_t = logic,
  parameter type dma_resp_t = logic,
  parameter type l2_req_t = logic,
  parameter type l2_resp_t = logic,
  // Dependent parameters, do not override!
  parameter type addr_t = logic [AddrWidth-1:0]
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,

  input  addr_t                       l2_start_addr_i,
  input  addr_t                       l2_end_addr_i,

  input  dma_req_t  [NumClusters-1:0] dma_req_i,
  output dma_resp_t [NumClusters-1:0] dma_resp_o,

  output l2_req_t                     l2_req_o,
  input  l2_resp_t                    l2_resp_i
);

  // Types of ports.
  typedef logic [DataWidth-1:0]   data_t;
  typedef logic [DataWidth/8-1:0] strb_t;
  typedef logic [DMAIdWidth-1:0]  dma_id_t;
  typedef logic [L2IdWidth-1:0]   l2_id_t;
  typedef logic [UserWidth-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(dma_aw_t, addr_t, dma_id_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(l2_aw_t, addr_t, l2_id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(dma_b_t, dma_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(l2_b_t, l2_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(dma_ar_t, addr_t, dma_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(l2_ar_t, addr_t, l2_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(dma_r_t, data_t, dma_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(l2_r_t, data_t, l2_id_t, user_t)

  // Types of master ports of multiplexer.
  parameter int unsigned MuxIdWidth = DMAIdWidth + cf_math_pkg::idx_width(NumClusters);
  typedef logic [MuxIdWidth-1:0] mux_id_t;
  `AXI_TYPEDEF_AW_CHAN_T(mux_aw_t, addr_t, mux_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mux_b_t, mux_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mux_ar_t, addr_t, mux_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mux_r_t, data_t, mux_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(mux_req_t, mux_aw_t, w_t, mux_ar_t)
  `AXI_TYPEDEF_RESP_T(mux_resp_t, mux_b_t, mux_r_t)
  mux_req_t  mux_req;
  mux_resp_t mux_resp;

  // Instantiation of multiplexer.
  axi_mux #(
    .SlvAxiIDWidth  (DMAIdWidth),
    .slv_aw_chan_t  (dma_aw_t),
    .mst_aw_chan_t  (mux_aw_t),
    .w_chan_t       (w_t),
    .slv_b_chan_t   (dma_b_t),
    .mst_b_chan_t   (mux_b_t),
    .slv_ar_chan_t  (dma_ar_t),
    .mst_ar_chan_t  (mux_ar_t),
    .slv_r_chan_t   (dma_r_t),
    .mst_r_chan_t   (mux_r_t),
    .slv_req_t      (dma_req_t),
    .slv_resp_t     (dma_resp_t),
    .mst_req_t      (mux_req_t),
    .mst_resp_t     (mux_resp_t),
    .NoSlvPorts     (NumClusters),
    .MaxWTrans      (8),  // TODO: calibrate
    .FallThrough    (1'b0),
    .SpillAw        (1'b0),
    .SpillW         (1'b0),
    .SpillB         (1'b0),
    .SpillAr        (1'b0),
    .SpillR         (1'b0)
  ) i_mux (
    .clk_i,
    .rst_ni,
    .test_i       (1'b0),
    .slv_reqs_i   (dma_req_i),
    .slv_resps_o  (dma_resp_o),
    .mst_req_o    (mux_req),
    .mst_resp_i   (mux_resp)
  );

  // ID width converter towards L2.
  axi_id_remap #(
    .AxiSlvPortIdWidth    (MuxIdWidth),
    .AxiMstPortIdWidth    (L2IdWidth),
    .AxiSlvPortMaxUniqIds (8),  // TODO: calibrate
    .AxiMaxTxnsPerId      (2),  // TODO: calibrate (=depth of store buffer?)
    .slv_req_t            (mux_req_t),
    .slv_resp_t           (mux_resp_t),
    .mst_req_t            (l2_req_t),
    .mst_resp_t           (l2_resp_t)
  ) i_iw_converter_l2 (
    .clk_i,
    .rst_ni,
    .slv_req_i  (mux_req),
    .slv_resp_o (mux_resp),
    .mst_req_o  (l2_req_o),
    .mst_resp_i (l2_resp_i)
  );

endmodule
