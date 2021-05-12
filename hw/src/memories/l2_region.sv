// Copyright (c) 2021 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module l2_region 
  import pspin_cfg_pkg::*;
(
    
);

  //*******************//
  // L2 program memory //
  //*******************//

  internal_wide_req_t    host_l2_prog_req;
  internal_wide_resp_t   host_l2_prog_resp;
  internal_narrow_req_t  host_slv_downsized_req;
  internal_narrow_resp_t host_slv_downsized_resp;

  prog_mem #(
    .NumClusters  (N_CLUSTERS),
    .NumBytes     (L2_PROG_SIZE),
    .AddrWidth    (AXI_INTERNAL_AW),
    .DataWidth    (AXI_NARROW_DW),
    .IdWidth      (AXI_IW),
    .UserWidth    (AXI_UW),
    .req_t        (internal_narrow_req_t),
    .resp_t       (internal_narrow_resp_t)
  ) i_prog_mem (
    .clk_i        ( clk_i                   ),
    .rst_ni       ( rst_ni                  ),
    .cl_req_i     ( cl_icache_req           ),
    .cl_resp_o    ( cl_icache_resp          ),
    .host_req_i   ( host_slv_downsized_req  ),
    .host_resp_o  ( host_slv_downsized_resp )
  );

  axi_dw_downsizer #(
    .AxiMaxReads         ( 4                                    ), // Number of outstanding reads
    .AxiSlvPortDataWidth ( pspin_cfg_pkg::AXI_WIDE_DW           ), // Data width of the slv port
    .AxiMstPortDataWidth ( pulp_cluster_cfg_pkg::AXI_DW_ICACHE  ), // Data width of the mst port
    .AxiAddrWidth        ( pulp_cluster_cfg_pkg::AXI_AW         ), // Address width
    .AxiIdWidth          ( pspin_cfg_pkg::AXI_IW                ), // ID width
    .aw_chan_t           ( pspin_cfg_pkg::aw_t                  ), // AW Channel Type
    .mst_w_chan_t        ( pulp_cluster_cfg_pkg::w_icache_t     ), //  W Channel Type for the mst port
    .slv_w_chan_t        ( pspin_cfg_pkg::w_t                   ), //  W Channel Type for the slv port
    .b_chan_t            ( pspin_cfg_pkg::b_t                   ), //  B Channel Type
    .ar_chan_t           ( pspin_cfg_pkg::ar_t                  ), // AR Channel Type
    .mst_r_chan_t        ( pulp_cluster_cfg_pkg::r_icache_t     ), //  R Channel Type for the mst port
    .slv_r_chan_t        ( pspin_cfg_pkg::r_t                   ), //  R Channel Type for the slv port
    .axi_mst_req_t       ( pulp_cluster_cfg_pkg::req_icache_t   ), // AXI Request Type for mst ports
    .axi_mst_resp_t      ( pulp_cluster_cfg_pkg::resp_icache_t  ), // AXI Response Type for mst ports
    .axi_slv_req_t       ( pspin_cfg_pkg::req_t                 ), // AXI Request Type for slv ports
    .axi_slv_resp_t      ( pspin_cfg_pkg::resp_t                )  // AXI Response Type for slv ports
  ) i_dw_downsizer_host_l2_prog (
    .clk_i               ( clk_i                                ),
    .rst_ni              ( rst_ni                               ),
    .slv_req_i           ( host_l2_prog_req                     ),
    .slv_resp_o          ( host_l2_prog_resp                    ), 
    .mst_req_o           ( host_slv_downsized_req               ),
    .mst_resp_i          ( host_slv_downsized_resp              )
  );

  //*******************//
  // L2 handler memory //
  //*******************//
  
  l2_mem #(
    .AXI_AW         (AXI_AW),
    .AXI_DW         (AXI_WIDE_DW),
    .AXI_UW         (AXI_UW),
    .AXI_IW         (AXI_IW),
    .N_BYTES        (HND_MEM_SIZE),
    .CUT_DW         (64),
    .CUT_N_WORDS    (16384),
    .N_PAR_CUTS_MUL (4)
  ) i_l2_hnd_mem (
    .clk_i,
    .rst_ni,
    .slv_a    (l2_hnd_mst_wo_atomics),
    .slv_b    (l2_hnd_mst_b)
  );

  axi_riscv_atomics_wrap #(
    .AXI_ADDR_WIDTH     (AXI_AW),
    .AXI_DATA_WIDTH     (AXI_WIDE_DW),
    .AXI_ID_WIDTH       (AXI_IW),
    .AXI_USER_WIDTH     (AXI_UW),
    .AXI_MAX_READ_TXNS  (4),
    .AXI_MAX_WRITE_TXNS (4),
    .RISCV_WORD_WIDTH   (32)
  ) i_atomics (
    .clk_i,
    .rst_ni,
    .slv    (l2_hnd_mst_a),
    .mst    (l2_hnd_mst_wo_atomics)
  );

  //******************//
  // L2 packet memory //
  //******************//

  l2_mem #(
    .AXI_AW         (AXI_AW),
    .AXI_DW         (AXI_WIDE_DW),
    .AXI_UW         (AXI_UW),
    .AXI_IW         (AXI_IW),
    .N_BYTES        (PKT_MEM_SIZE),
    .CUT_DW         (512),
    .CUT_N_WORDS    (2048),
    .N_PAR_CUTS_MUL (32)
  ) i_l2_pkt_mem (
    .clk_i,
    .rst_ni,
    .slv_a    (l2_pkt_mst_a),
    .slv_b    (l2_pkt_mst_b)
  );

  //*******************//
  // L2 crossbar //
  //*******************//

  l2_xbar #(
    .AddrWidth  (AXI_AW),
    .DataWidth  (AXI_WIDE_DW),
    .IdWidth    (AXI_IW),
    .UserWidth  (AXI_UW),
    .req_t      (req_t),
    .resp_t     (resp_t)
  ) i_l2_xbar (
    .clk_i,
    .rst_ni,
    .l2_hnd_start_addr_i  (l2_hnd_start_addr),
    .l2_hnd_end_addr_i    (l2_hnd_end_addr),
    .l2_pkt_start_addr_i  (l2_pkt_start_addr),
    .l2_pkt_end_addr_i    (l2_pkt_end_addr),
    .pe_req_i             (pe_l2_req),
    .pe_resp_o            (pe_l2_resp),
    .dma_req_i            (dma_l2_req),
    .dma_resp_o           (dma_l2_resp),
    .l2_hnd_req_o         (l2_hnd_req_a),
    .l2_hnd_resp_i        (l2_hnd_resp_a),
    .l2_pkt_req_o         (l2_pkt_req_a),
    .l2_pkt_resp_i        (l2_pkt_resp_a)
  );

endmodule