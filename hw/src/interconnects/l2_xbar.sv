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

module l2_xbar #(
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

  input  req_t  pe_req_i,
  output resp_t pe_resp_o,
  input  req_t  ptw_req_i,
  output resp_t ptw_resp_o,
  input  req_t  dma_req_i,
  output resp_t dma_resp_o,

  output req_t  l2_hnd_req_o,
  input  resp_t l2_hnd_resp_i,
  output req_t  l2_pkt_req_o,
  input  resp_t l2_pkt_resp_i
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
  rule_t [1:0] addr_map;
  assign addr_map[0] = '{
    idx:        0,
    start_addr: l2_hnd_start_addr_i,
    end_addr:   l2_hnd_end_addr_i
  };
  assign addr_map[1] = '{
    idx:        1,
    start_addr: l2_pkt_start_addr_i,
    end_addr:   l2_pkt_end_addr_i
  };

  // PE demultiplexer
  logic pe_aw_idx, pe_ar_idx,
        pe_aw_err, pe_ar_err;
  addr_decode #(
    .NoIndices  (2),
    .NoRules    (2),
    .addr_t     (addr_t),
    .rule_t     (rule_t)
  ) i_decode_pe_aw (
    .addr_i           (pe_req_i.aw.addr),
    .addr_map_i       (addr_map),
    .idx_o            (pe_aw_idx),
    .dec_valid_o      (/* unused */),
    .dec_error_o      (pe_aw_err),
    .en_default_idx_i (1'b0),
    .default_idx_i    ('0)
  );
  addr_decode #(
    .NoIndices  (2),
    .NoRules    (2),
    .addr_t     (addr_t),
    .rule_t     (rule_t)
  ) i_decode_pe_ar (
    .addr_i           (pe_req_i.ar.addr),
    .addr_map_i       (addr_map),
    .idx_o            (pe_ar_idx),
    .dec_valid_o      (/* unused */),
    .dec_error_o      (pe_ar_err),
    .en_default_idx_i (1'b0),
    .default_idx_i    ('0)
  );
  req_t   pe_err_req,   pe_pkt_req,   pe_hnd_req;
  resp_t  pe_err_resp,  pe_pkt_resp,  pe_hnd_resp;
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
  ) i_mux_pe (
    .clk_i,
    .rst_ni,
    .test_i           (1'b0),
    .slv_req_i        (pe_req_i),
    .slv_aw_select_i  ({pe_aw_err, pe_aw_idx}),
    .slv_ar_select_i  ({pe_ar_err, pe_ar_idx}),
    .slv_resp_o       (pe_resp_o),
    .mst_reqs_o       ({pe_err_req,   pe_pkt_req,   pe_hnd_req}),
    .mst_resps_i      ({pe_err_resp,  pe_pkt_resp,  pe_hnd_resp})
  );
  axi_err_slv #(
    .AxiIdWidth (IdWidth),
    .req_t      (req_t),
    .resp_t     (resp_t),
    .Resp       (axi_pkg::RESP_DECERR),
    .ATOPs      (1'b1),
    .MaxTrans   (4)
  ) i_pe_err_slv (
    .clk_i,
    .rst_ni,
    .test_i     (1'b0),
    .slv_req_i  (pe_err_req),
    .slv_resp_o (pe_err_resp)
  );

  // DMA demultiplexer
  logic dma_aw_idx, dma_ar_idx,
        dma_aw_err, dma_ar_err;
  addr_decode #(
    .NoIndices  (2),
    .NoRules    (2),
    .addr_t     (addr_t),
    .rule_t     (rule_t)
  ) i_decode_dma_aw (
    .addr_i           (dma_req_i.aw.addr),
    .addr_map_i       (addr_map),
    .idx_o            (dma_aw_idx),
    .dec_valid_o      (/* unused */),
    .dec_error_o      (dma_aw_err),
    .en_default_idx_i (1'b0),
    .default_idx_i    ('0)
  );
  addr_decode #(
    .NoIndices  (2),
    .NoRules    (2),
    .addr_t     (addr_t),
    .rule_t     (rule_t)
  ) i_decode_dma_ar (
    .addr_i           (dma_req_i.ar.addr),
    .addr_map_i       (addr_map),
    .idx_o            (dma_ar_idx),
    .dec_valid_o      (/* unused */),
    .dec_error_o      (dma_ar_err),
    .en_default_idx_i (1'b0),
    .default_idx_i    ('0)
  );
  req_t   dma_err_req,   dma_pkt_req,   dma_hnd_req;
  resp_t  dma_err_resp,  dma_pkt_resp,  dma_hnd_resp;
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
  ) i_mux_dma (
    .clk_i,
    .rst_ni,
    .test_i           (1'b0),
    .slv_req_i        (dma_req_i),
    .slv_aw_select_i  ({dma_aw_err, dma_aw_idx}),
    .slv_ar_select_i  ({dma_ar_err, dma_ar_idx}),
    .slv_resp_o       (dma_resp_o),
    .mst_reqs_o       ({dma_err_req,   dma_pkt_req,   dma_hnd_req}),
    .mst_resps_i      ({dma_err_resp,  dma_pkt_resp,  dma_hnd_resp})
  );
  axi_err_slv #(
    .AxiIdWidth (IdWidth),
    .req_t      (req_t),
    .resp_t     (resp_t),
    .Resp       (axi_pkg::RESP_DECERR),
    .ATOPs      (1'b0),
    .MaxTrans   (4)
  ) i_dma_err_slv (
    .clk_i,
    .rst_ni,
    .test_i     (1'b0),
    .slv_req_i  (dma_err_req),
    .slv_resp_o (dma_err_resp)
  );


  // Types of master ports of multiplexers.
  parameter int unsigned HndNumSlvPorts = 3;
  parameter int unsigned PktNumSlvPorts = 2;
  parameter int unsigned HndMuxIdWidth = IdWidth + cf_math_pkg::idx_width(HndNumSlvPorts);
  parameter int unsigned PktMuxIdWidth = IdWidth + cf_math_pkg::idx_width(PktNumSlvPorts);

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
    .slv_reqs_i   ({dma_hnd_req,  pe_hnd_req, ptw_req_i}),
    .slv_resps_o  ({dma_hnd_resp, pe_hnd_resp, ptw_resp_o}),
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
    .slv_reqs_i   ({dma_pkt_req,  pe_pkt_req}),
    .slv_resps_o  ({dma_pkt_resp, pe_pkt_resp}),
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

endmodule