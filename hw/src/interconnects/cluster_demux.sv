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

module cluster_demux #(
  parameter int unsigned NumClusters = 0,
  parameter int unsigned AddrWidth = 0,
  parameter int unsigned DataWidth = 0,
  parameter int unsigned UserWidth = 0,
  parameter int unsigned NHIIdWidth = 0,
  parameter int unsigned ClIdWidth = 0,
  parameter type nhi_req_t = logic,
  parameter type nhi_resp_t = logic,
  parameter type cl_req_t = logic,
  parameter type cl_resp_t = logic,
  // Dependent parameters, do not override!
  parameter type addr_t = logic [AddrWidth-1:0]
) (
  input  logic                                 clk_i,
  input  logic                                 rst_ni,

  input  addr_t [NumClusters-1:0]              cl_start_addr_i,
  input  addr_t [NumClusters-1:0]              cl_end_addr_i,

  output cl_req_t  [NumClusters-1:0]           cl_req_o,
  input  cl_resp_t [NumClusters-1:0]           cl_resp_i,

  input  nhi_req_t                             nhi_req_i,
  output nhi_resp_t                            nhi_resp_o
);

  // Types of input and output channels.
  typedef logic [DataWidth-1:0]   data_t;
  typedef logic [DataWidth/8-1:0] strb_t;
  typedef logic [ClIdWidth-1:0]  id_t;
  typedef logic [UserWidth-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_t, data_t, id_t, user_t)


  // Addressing rules
  typedef struct packed {
    int unsigned  idx;
    addr_t        start_addr;
    addr_t        end_addr;
  } rule_t;

  localparam ClusterIdWidth = cf_math_pkg::idx_width(NumClusters);
  localparam MstIdWidth = cf_math_pkg::idx_width(NumClusters + 1);

  // Address map of crossbar.
  rule_t [NumClusters-1:0] addr_map;
  for (genvar i = 0; i < NumClusters; i++) begin : gen_addr_map
    assign addr_map[i].idx = unsigned'(i);
    assign addr_map[i].start_addr = cl_start_addr_i[i];
    assign addr_map[i].end_addr = cl_end_addr_i[i];
  end

  logic [ClusterIdWidth-1:0] nhi_aw_idx;
  logic [ClusterIdWidth-1:0] nhi_ar_idx;
  logic [MstIdWidth-1:0] nhi_ar_select;
  logic [MstIdWidth-1:0] nhi_aw_select;
  logic nhi_aw_err, nhi_ar_err;

  cl_req_t nhi_req;
  cl_resp_t nhi_resp;

  axi_id_remap #(
    .AxiSlvPortIdWidth    (NHIIdWidth),
    .AxiMstPortIdWidth    (ClIdWidth),
    .AxiSlvPortMaxUniqIds (8),  // TODO: calibrate
    .AxiMaxTxnsPerId      (2),  // TODO: calibrate (=depth of store buffer?)
    .slv_req_t            (nhi_req_t),
    .slv_resp_t           (nhi_resp_t),
    .mst_req_t            (cl_req_t),
    .mst_resp_t           (cl_resp_t)
  ) i_iw_converter_cluster (
    .clk_i,
    .rst_ni,
    .slv_req_i  (nhi_req_i),
    .slv_resp_o (nhi_resp_o),
    .mst_req_o  (nhi_req),
    .mst_resp_i (nhi_resp)
  );

  addr_decode #(
    .NoIndices  (NumClusters),
    .NoRules    (NumClusters),
    .addr_t     (addr_t),
    .rule_t     (rule_t)
  ) i_decode_nhi_aw (
    .addr_i           (nhi_req.aw.addr),
    .addr_map_i       (addr_map),
    .idx_o            (nhi_aw_idx),
    .dec_valid_o      (/* unused */),
    .dec_error_o      (nhi_aw_err),
    .en_default_idx_i (1'b0),
    .default_idx_i    ('0)
  );

  addr_decode #(
    .NoIndices  (NumClusters),
    .NoRules    (NumClusters),
    .addr_t     (addr_t),
    .rule_t     (rule_t)
  ) i_decode_nhi_ar (
    .addr_i           (nhi_req.ar.addr),
    .addr_map_i       (addr_map),
    .idx_o            (nhi_ar_idx),
    .dec_valid_o      (/* unused */),
    .dec_error_o      (nhi_ar_err),
    .en_default_idx_i (1'b0),
    .default_idx_i    ('0)
  );

  assign nhi_aw_select = (nhi_aw_err) ? NumClusters : nhi_aw_idx;
  assign nhi_ar_select = (nhi_ar_err) ? NumClusters : nhi_ar_idx;

  cl_req_t  nhi_err_req;
  cl_resp_t nhi_err_resp;

  axi_demux #(
    .AxiIdWidth   (ClIdWidth),
    .aw_chan_t    (aw_t),
    .w_chan_t     (w_t),
    .b_chan_t     (b_t),
    .ar_chan_t    (ar_t),
    .r_chan_t     (r_t),
    .req_t        (cl_req_t),
    .resp_t       (cl_resp_t),
    .NoMstPorts   (NumClusters + 1),
    .MaxTrans     (8), // TODO: calibrate
    .AxiLookBits  (ClIdWidth),
    .FallThrough  (1'b1),
    .SpillAw      (1'b0),
    .SpillW       (1'b0),
    .SpillB       (1'b0),
    .SpillAr      (1'b0),
    .SpillR       (1'b0)
  ) i_mux_nhi (
    .clk_i,
    .rst_ni,
    .test_i           (1'b0),
    .slv_req_i        (nhi_req),
    .slv_aw_select_i  (nhi_aw_select),
    .slv_ar_select_i  (nhi_ar_select),
    .slv_resp_o       (nhi_resp),
    .mst_reqs_o       ({nhi_err_req,  cl_req_o}),
    .mst_resps_i      ({nhi_err_resp, cl_resp_i})
  );

  axi_err_slv #(
    .AxiIdWidth (ClIdWidth),
    .req_t      (cl_req_t),
    .resp_t     (cl_resp_t),
    .Resp       (axi_pkg::RESP_DECERR),
    .ATOPs      (1'b1),
    .MaxTrans   (4)
  ) i_edma_err_slv (
    .clk_i,
    .rst_ni,
    .test_i     (1'b0),
    .slv_req_i  (nhi_err_req),
    .slv_resp_o (nhi_err_resp)
  );


endmodule