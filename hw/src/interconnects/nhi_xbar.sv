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

module nhi_xbar #(
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

  input  addr_t l2_hnd_start_addr_i,
  input  addr_t l2_hnd_end_addr_i,
  
  input  addr_t l2_pkt_start_addr_i,
  input  addr_t l2_pkt_end_addr_i,
  
  input  addr_t l2_prog_start_addr_i,
  input  addr_t l2_prog_end_addr_i,

  input  addr_t l1_start_addr_i,
  input  addr_t l1_end_addr_i,

  //from HOST mst
  input  req_t  host_req_i,
  output resp_t host_resp_o,

  //from NIC inbound
  input  req_t  ni_req_i,
  output resp_t ni_resp_o,

  //from NIC outbound
  input  req_t  no_req_i,
  output resp_t no_resp_o,

  //from DMA cluster (external/off-cluster DMA)
  input  req_t  edma_req_i,
  output resp_t edma_resp_o,

  //to L2 handler mem
  output req_t  l2_hnd_req_o,
  input  resp_t l2_hnd_resp_i,

  //to L2 pkt mem
  output req_t  l2_pkt_req_o,
  input  resp_t l2_pkt_resp_i,
 
  //to L2 prog mem
  output req_t  l2_prog_req_o,
  input  resp_t l2_prog_resp_i,

  //to TCDMs into clusters
  output req_t  cluster_req_o,
  input  resp_t cluster_resp_i
);

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

  // Addressing rules
  typedef struct packed {
    int unsigned  idx;
    addr_t        start_addr;
    addr_t        end_addr;
  } rule_t;

  //Define addressing rules
  rule_t [1:0] host_addr_map;
  assign host_addr_map[0] = '{
    idx:        0,
    start_addr: l2_hnd_start_addr_i,
    end_addr:   l2_hnd_end_addr_i
  };

  assign host_addr_map[1] = '{
    idx:        1,
    start_addr: l2_prog_start_addr_i,
    end_addr:   l2_prog_end_addr_i
  };

  rule_t [2:0] nic_edma_addr_map;
  assign nic_edma_addr_map[0] = '{
    idx:        0,
    start_addr: l2_hnd_start_addr_i,
    end_addr:   l2_hnd_end_addr_i
  };

  assign nic_edma_addr_map[1] = '{
    idx:        1,
    start_addr: l2_pkt_start_addr_i,
    end_addr:   l2_pkt_end_addr_i
  };

  assign nic_edma_addr_map[2] = '{
    idx:        2,
    start_addr: l1_start_addr_i,
    end_addr:   l1_end_addr_i
  };

  //Host mst demux
  logic host_aw_idx, host_ar_idx,
        host_aw_err, host_ar_err;

  addr_decode #(
    .NoIndices  (2),
    .NoRules    (2),
    .addr_t     (addr_t),
    .rule_t     (rule_t)
  ) i_decode_host_aw (
    .addr_i           (host_req_i.aw.addr),
    .addr_map_i       (host_addr_map),
    .idx_o            (host_aw_idx),
    .dec_valid_o      (/* unused */),
    .dec_error_o      (host_aw_err),
    .en_default_idx_i (1'b0),
    .default_idx_i    ('0)
  );

  addr_decode #(
    .NoIndices  (2),
    .NoRules    (2),
    .addr_t     (addr_t),
    .rule_t     (rule_t)
  ) i_decode_host_ar (
    .addr_i           (host_req_i.ar.addr),
    .addr_map_i       (host_addr_map),
    .idx_o            (host_ar_idx),
    .dec_valid_o      (/* unused */),
    .dec_error_o      (host_ar_err),
    .en_default_idx_i (1'b0),
    .default_idx_i    ('0)
  );

  req_t   host_err_req,   host_prog_req,   host_hnd_req;
  resp_t  host_err_resp,  host_prog_resp,  host_hnd_resp;
  axi_demux #(
    .AxiIdWidth   (IdWidth),
    .aw_chan_t    (aw_t),
    .w_chan_t     (w_t),
    .b_chan_t     (b_t),
    .ar_chan_t    (ar_t),
    .r_chan_t     (r_t),
    .req_t        (req_t),
    .resp_t       (resp_t),
    .NoMstPorts   (3),
    .MaxTrans     (8), // TODO: calibrate
    .AxiLookBits  (IdWidth),
    .FallThrough  (1'b1),
    .SpillAw      (1'b0),
    .SpillW       (1'b0),
    .SpillB       (1'b0),
    .SpillAr      (1'b0),
    .SpillR       (1'b0)
  ) i_demux_host (
    .clk_i,
    .rst_ni,
    .test_i           (1'b0),
    .slv_req_i        (host_req_i),
    .slv_aw_select_i  ({host_aw_err, host_aw_idx}),
    .slv_ar_select_i  ({host_ar_err, host_ar_idx}),
    .slv_resp_o       (host_resp_o),
    .mst_reqs_o       ({host_err_req,  host_prog_req,  host_hnd_req}),
    .mst_resps_i      ({host_err_resp, host_prog_resp, host_hnd_resp})
  );

  axi_err_slv #(
    .AxiIdWidth (IdWidth),
    .req_t      (req_t),
    .resp_t     (resp_t),
    .Resp       (axi_pkg::RESP_DECERR),
    .ATOPs      (1'b1),
    .MaxTrans   (4)
  ) i_host_err_slv (
    .clk_i,
    .rst_ni,
    .test_i     (1'b0),
    .slv_req_i  (host_err_req),
    .slv_resp_o (host_err_resp)
  );

  // Request to program memory are not multiplexed 
  assign l2_prog_req_o = host_prog_req;
  assign host_prog_resp = l2_prog_resp_i;

  //NIC outbound demux
  logic [1:0] no_aw_idx;
  logic [1:0] no_ar_idx;
  logic no_aw_err, no_ar_err;

  addr_decode #(
    .NoIndices  (3),
    .NoRules    (3),
    .addr_t     (addr_t),
    .rule_t     (rule_t)
  ) i_decode_no_aw (
    .addr_i           (no_req_i.aw.addr),
    .addr_map_i       (nic_edma_addr_map),
    .idx_o            (no_aw_idx),
    .dec_valid_o       (/* unused */),
    .dec_error_o      (no_aw_err),
    .en_default_idx_i (1'b0),
    .default_idx_i    ('0)
  );

  addr_decode #(
    .NoIndices  (3),
    .NoRules    (3),
    .addr_t     (addr_t),
    .rule_t     (rule_t)
  ) i_decode_no_ar (
    .addr_i           (no_req_i.ar.addr),
    .addr_map_i       (nic_edma_addr_map),
    .idx_o            (no_ar_idx),
    .dec_valid_o      (/* unused */),
    .dec_error_o      (no_ar_err),
    .en_default_idx_i (1'b0),
    .default_idx_i    ('0)
  );

  parameter int unsigned NicOutboundNumMstPorts = 3;
  parameter int unsigned NicOutboundMstIdx = cf_math_pkg::idx_width(NicOutboundNumMstPorts + 1);
  
  logic [NicOutboundMstIdx-1:0] no_aw_select;
  logic [NicOutboundMstIdx-1:0] no_ar_select;

  assign no_aw_select = (no_aw_err) ? NicOutboundNumMstPorts : no_aw_idx;
  assign no_ar_select = (no_ar_err) ? NicOutboundNumMstPorts : no_ar_idx;

  req_t   no_err_req,  no_cluster_req,  no_pkt_req,  no_hnd_req;
  resp_t  no_err_resp, no_cluster_resp, no_pkt_resp, no_hnd_resp;
  axi_demux #(
    .AxiIdWidth   (IdWidth),
    .aw_chan_t    (aw_t),
    .w_chan_t     (w_t),
    .b_chan_t     (b_t),
    .ar_chan_t    (ar_t),
    .r_chan_t     (r_t),
    .req_t        (req_t),
    .resp_t       (resp_t),
    .NoMstPorts   (NicOutboundNumMstPorts + 1),
    .MaxTrans     (8), // TODO: calibrate
    .AxiLookBits  (IdWidth),
    .FallThrough  (1'b1),
    .SpillAw      (1'b0),
    .SpillW       (1'b0),
    .SpillB       (1'b0),
    .SpillAr      (1'b0),
    .SpillR       (1'b0)
  ) i_demux_no (
    .clk_i,
    .rst_ni,
    .test_i           (1'b0),
    .slv_req_i        (no_req_i),
    .slv_aw_select_i  (no_aw_select),
    .slv_ar_select_i  (no_ar_select),
    .slv_resp_o       (no_resp_o),
    .mst_reqs_o       ({no_err_req,  no_cluster_req,  no_pkt_req,  no_hnd_req}),
    .mst_resps_i      ({no_err_resp, no_cluster_resp, no_pkt_resp, no_hnd_resp})
  );

  axi_err_slv #(
    .AxiIdWidth (IdWidth),
    .req_t      (req_t),
    .resp_t     (resp_t),
    .Resp       (axi_pkg::RESP_DECERR),
    .ATOPs      (1'b1),
    .MaxTrans   (4)
  ) i_no_err_slv (
    .clk_i,
    .rst_ni,
    .test_i     (1'b0),
    .slv_req_i  (no_err_req),
    .slv_resp_o (no_err_resp)
  );

  //DMA (off-cluster) demux
  logic [1:0] edma_aw_idx;
  logic [1:0] edma_ar_idx;
  logic edma_aw_err, edma_ar_err;

  addr_decode #(
    .NoIndices  (3),
    .NoRules    (3),
    .addr_t     (addr_t),
    .rule_t     (rule_t)
  ) i_decode_edma_aw (
    .addr_i           (edma_req_i.aw.addr),
    .addr_map_i       (nic_edma_addr_map),
    .idx_o            (edma_aw_idx),
    .dec_valid_o      (/* unused */),
    .dec_error_o      (edma_aw_err),
    .en_default_idx_i (1'b0),
    .default_idx_i    ('0)
  );

  addr_decode #(
    .NoIndices  (3),
    .NoRules    (3),
    .addr_t     (addr_t),
    .rule_t     (rule_t)
  ) i_decode_edma_ar (
    .addr_i           (edma_req_i.ar.addr),
    .addr_map_i       (nic_edma_addr_map),
    .idx_o            (edma_ar_idx),
    .dec_valid_o      (/* unused */),
    .dec_error_o      (edma_ar_err),
    .en_default_idx_i (1'b0),
    .default_idx_i    ('0)
  );

  parameter int unsigned EdmaNumMstPorts = 3;
  parameter int unsigned EdmaMstIdx = cf_math_pkg::idx_width(EdmaNumMstPorts + 1);
  
  logic [EdmaMstIdx-1:0] edma_aw_select;
  logic [EdmaMstIdx-1:0] edma_ar_select;

  assign edma_aw_select = (edma_aw_err) ? EdmaNumMstPorts : edma_aw_idx;
  assign edma_ar_select = (edma_ar_err) ? EdmaNumMstPorts : edma_ar_idx;

  req_t   edma_err_req,  edma_cluster_req,  edma_pkt_req,  edma_hnd_req;
  resp_t  edma_err_resp, edma_cluster_resp, edma_pkt_resp, edma_hnd_resp;
  axi_demux #(
    .AxiIdWidth   (IdWidth),
    .aw_chan_t    (aw_t),
    .w_chan_t     (w_t),
    .b_chan_t     (b_t),
    .ar_chan_t    (ar_t),
    .r_chan_t     (r_t),
    .req_t        (req_t),
    .resp_t       (resp_t),
    .NoMstPorts   (EdmaNumMstPorts + 1),
    .MaxTrans     (8), // TODO: calibrate
    .AxiLookBits  (IdWidth),
    .FallThrough  (1'b1),
    .SpillAw      (1'b0),
    .SpillW       (1'b0),
    .SpillB       (1'b0),
    .SpillAr      (1'b0),
    .SpillR       (1'b0)
  ) i_demux_edma (
    .clk_i,
    .rst_ni,
    .test_i           (1'b0),
    .slv_req_i        (edma_req_i),
    .slv_aw_select_i  (edma_aw_select),
    .slv_ar_select_i  (edma_ar_select),
    .slv_resp_o       (edma_resp_o),
    .mst_reqs_o       ({edma_err_req,  edma_cluster_req,  edma_pkt_req,  edma_hnd_req}),
    .mst_resps_i      ({edma_err_resp, edma_cluster_resp, edma_pkt_resp, edma_hnd_resp})
  );

  axi_err_slv #(
    .AxiIdWidth (IdWidth),
    .req_t      (req_t),
    .resp_t     (resp_t),
    .Resp       (axi_pkg::RESP_DECERR),
    .ATOPs      (1'b1),
    .MaxTrans   (4)
  ) i_edma_err_slv (
    .clk_i,
    .rst_ni,
    .test_i     (1'b0),
    .slv_req_i  (edma_err_req),
    .slv_resp_o (edma_err_resp)
  );

  // Types of master ports of multiplexers.
  parameter int unsigned HndNumSlvPorts = 3;
  parameter int unsigned PktNumSlvPorts = 3;
  parameter int unsigned ClusterNumSlvPorts = 2;
  parameter int unsigned HndMuxIdWidth = IdWidth + cf_math_pkg::idx_width(HndNumSlvPorts);
  parameter int unsigned PktMuxIdWidth = IdWidth + cf_math_pkg::idx_width(PktNumSlvPorts);
  parameter int unsigned ClusterMuxIdWidth = IdWidth + cf_math_pkg::idx_width(ClusterNumSlvPorts);

  typedef logic [HndMuxIdWidth-1:0] hnd_mux_id_t;
  `AXI_TYPEDEF_AW_CHAN_T(hnd_mux_aw_t, addr_t, hnd_mux_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(hnd_mux_b_t, hnd_mux_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(hnd_mux_ar_t, addr_t, hnd_mux_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(hnd_mux_r_t, data_t, hnd_mux_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(hnd_mux_req_t, hnd_mux_aw_t, w_t, hnd_mux_ar_t)
  `AXI_TYPEDEF_RESP_T(hnd_mux_resp_t, hnd_mux_b_t, hnd_mux_r_t)
  hnd_mux_req_t  hnd_mux_req;
  hnd_mux_resp_t hnd_mux_resp;

  typedef logic [PktMuxIdWidth-1:0] pkt_mux_id_t;
  `AXI_TYPEDEF_AW_CHAN_T(pkt_mux_aw_t, addr_t, pkt_mux_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(pkt_mux_b_t, pkt_mux_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(pkt_mux_ar_t, addr_t, pkt_mux_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(pkt_mux_r_t, data_t, pkt_mux_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(pkt_mux_req_t, pkt_mux_aw_t, w_t, pkt_mux_ar_t)
  `AXI_TYPEDEF_RESP_T(pkt_mux_resp_t, pkt_mux_b_t, pkt_mux_r_t)
  pkt_mux_req_t  pkt_mux_req;
  pkt_mux_resp_t pkt_mux_resp;

  typedef logic [ClusterMuxIdWidth-1:0] cluster_mux_id_t;
  `AXI_TYPEDEF_AW_CHAN_T(cluster_mux_aw_t, addr_t, cluster_mux_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(cluster_mux_b_t, cluster_mux_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(cluster_mux_ar_t, addr_t, cluster_mux_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(cluster_mux_r_t, data_t, cluster_mux_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(cluster_mux_req_t, cluster_mux_aw_t, w_t, cluster_mux_ar_t)
  `AXI_TYPEDEF_RESP_T(cluster_mux_resp_t, cluster_mux_b_t, cluster_mux_r_t)
  cluster_mux_req_t  cluster_mux_req;
  cluster_mux_resp_t cluster_mux_resp;

  // Multiplexer and ID width converter into handler L2.
  axi_mux #(
    .SlvAxiIDWidth  (IdWidth),
    .slv_aw_chan_t  (aw_t),
    .mst_aw_chan_t  (hnd_mux_aw_t),
    .w_chan_t       (w_t),
    .slv_b_chan_t   (b_t),
    .mst_b_chan_t   (hnd_mux_b_t),
    .slv_ar_chan_t  (ar_t),
    .mst_ar_chan_t  (hnd_mux_ar_t),
    .slv_r_chan_t   (r_t),
    .mst_r_chan_t   (hnd_mux_r_t),
    .slv_req_t      (req_t),
    .slv_resp_t     (resp_t),
    .mst_req_t      (hnd_mux_req_t),
    .mst_resp_t     (hnd_mux_resp_t),
    .NoSlvPorts     (HndNumSlvPorts),
    .MaxWTrans      (8),  // TODO: calibrate
    .FallThrough    (1'b0),
    .SpillAw        (1'b0),
    .SpillW         (1'b0),
    .SpillB         (1'b0),
    .SpillAr        (1'b0),
    .SpillR         (1'b0)
  ) i_hnd_mux (
    .clk_i,
    .rst_ni,
    .test_i       (1'b0),
    .slv_reqs_i   ({host_hnd_req,  no_hnd_req,  edma_hnd_req}),
    .slv_resps_o  ({host_hnd_resp, no_hnd_resp, edma_hnd_resp}),
    .mst_req_o    (hnd_mux_req),
    .mst_resp_i   (hnd_mux_resp)
  );

  axi_id_remap #(
    .AxiSlvPortIdWidth    (HndMuxIdWidth),
    .AxiMstPortIdWidth    (IdWidth),
    .AxiSlvPortMaxUniqIds (8),  // TODO: calibrate
    .AxiMaxTxnsPerId      (2),  // TODO: calibrate (=depth of store buffer?)
    .slv_req_t            (hnd_mux_req_t),
    .slv_resp_t           (hnd_mux_resp_t),
    .mst_req_t            (req_t),
    .mst_resp_t           (resp_t)
  ) i_hnd_iw_converter (
    .clk_i,
    .rst_ni,
    .slv_req_i  (hnd_mux_req),
    .slv_resp_o (hnd_mux_resp),
    .mst_req_o  (l2_hnd_req_o),
    .mst_resp_i (l2_hnd_resp_i)
  );

  // Multiplexer and ID width converter into packet L2.
  axi_mux #(
    .SlvAxiIDWidth  (IdWidth),
    .slv_aw_chan_t  (aw_t),
    .mst_aw_chan_t  (pkt_mux_aw_t),
    .w_chan_t       (w_t),
    .slv_b_chan_t   (b_t),
    .mst_b_chan_t   (pkt_mux_b_t),
    .slv_ar_chan_t  (ar_t),
    .mst_ar_chan_t  (pkt_mux_ar_t),
    .slv_r_chan_t   (r_t),
    .mst_r_chan_t   (pkt_mux_r_t),
    .slv_req_t      (req_t),
    .slv_resp_t     (resp_t),
    .mst_req_t      (pkt_mux_req_t),
    .mst_resp_t     (pkt_mux_resp_t),
    .NoSlvPorts     (PktNumSlvPorts),
    .MaxWTrans      (8),  // TODO: calibrate
    .FallThrough    (1'b0),
    .SpillAw        (1'b0),
    .SpillW         (1'b0),
    .SpillB         (1'b0),
    .SpillAr        (1'b0),
    .SpillR         (1'b0)
  ) i_pkt_mux (
    .clk_i,
    .rst_ni,
    .test_i       (1'b0),
    .slv_reqs_i   ({ni_req_i,  no_pkt_req,  edma_pkt_req}),
    .slv_resps_o  ({ni_resp_o, no_pkt_resp, edma_pkt_resp}),
    .mst_req_o    (pkt_mux_req),
    .mst_resp_i   (pkt_mux_resp)
  );

  axi_id_remap #(
    .AxiSlvPortIdWidth    (PktMuxIdWidth),
    .AxiMstPortIdWidth    (IdWidth),
    .AxiSlvPortMaxUniqIds (8),  // TODO: calibrate
    .AxiMaxTxnsPerId      (8),  // TODO: calibrate (bound by latency to SRAMs), 4 should be enough
    .slv_req_t            (pkt_mux_req_t),
    .slv_resp_t           (pkt_mux_resp_t),
    .mst_req_t            (req_t),
    .mst_resp_t           (resp_t)
  ) i_pkt_iw_converter (
    .clk_i,
    .rst_ni,
    .slv_req_i  (pkt_mux_req),
    .slv_resp_o (pkt_mux_resp),
    .mst_req_o  (l2_pkt_req_o),
    .mst_resp_i (l2_pkt_resp_i)
  );

  // Multiplexer and ID width converter into clusters' TCMDs.
  axi_mux #(
    .SlvAxiIDWidth  (IdWidth),
    .slv_aw_chan_t  (aw_t),
    .mst_aw_chan_t  (cluster_mux_aw_t),
    .w_chan_t       (w_t),
    .slv_b_chan_t   (b_t),
    .mst_b_chan_t   (cluster_mux_b_t),
    .slv_ar_chan_t  (ar_t),
    .mst_ar_chan_t  (cluster_mux_ar_t),
    .slv_r_chan_t   (r_t),
    .mst_r_chan_t   (cluster_mux_r_t),
    .slv_req_t      (req_t),
    .slv_resp_t     (resp_t),
    .mst_req_t      (cluster_mux_req_t),
    .mst_resp_t     (cluster_mux_resp_t),
    .NoSlvPorts     (ClusterNumSlvPorts),
    .MaxWTrans      (8),  // TODO: calibrate
    .FallThrough    (1'b0),
    .SpillAw        (1'b0),
    .SpillW         (1'b0),
    .SpillB         (1'b0),
    .SpillAr        (1'b0),
    .SpillR         (1'b0)
  ) i_cluster_mux (
    .clk_i,
    .rst_ni,
    .test_i       (1'b0),
    .slv_reqs_i   ({no_cluster_req,  edma_cluster_req}),
    .slv_resps_o  ({no_cluster_resp, edma_cluster_resp}),
    .mst_req_o    (cluster_mux_req),
    .mst_resp_i   (cluster_mux_resp)
  );

  axi_id_remap #(
    .AxiSlvPortIdWidth    (ClusterMuxIdWidth),
    .AxiMstPortIdWidth    (IdWidth),
    .AxiSlvPortMaxUniqIds (8),  // TODO: calibrate
    .AxiMaxTxnsPerId      (8),  // TODO: calibrate (bound by latency to SRAMs), 4 should be enough
    .slv_req_t            (cluster_mux_req_t),
    .slv_resp_t           (cluster_mux_resp_t),
    .mst_req_t            (req_t),
    .mst_resp_t           (resp_t)
  ) i_cluster_iw_converter (
    .clk_i,
    .rst_ni,
    .slv_req_i  (cluster_mux_req),
    .slv_resp_o (cluster_mux_resp),
    .mst_req_o  (cluster_req_o),
    .mst_resp_i (cluster_resp_i)
  );

endmodule
