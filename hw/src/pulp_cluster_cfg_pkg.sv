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

// Configuration package for PULP cluster OOC stub
package automatic pulp_cluster_cfg_pkg;
  // -- Decoupling of cluster clock domain
  localparam bit          ASYNC = 1'b0;
  localparam int unsigned DC_BUF_W = 8;
  // -- Cores
  localparam int unsigned N_CORES = 8; // must be a power of 2 and <= 8
  // -- AXI
  localparam int unsigned AXI_AW = 32; // [bit]
  localparam int unsigned AXI_DW = 64; // [bit]
  localparam int unsigned AXI_IW_MST = 6; // [bit]
  localparam int unsigned AXI_IW_SLV = 4; // [bit]
  localparam int unsigned AXI_UW = 4; // [bit]
  // -- DMA
  localparam int unsigned AXI_DMA_DW = 512; // [bit]; do not change
  localparam int unsigned AXI_DMA_IW = 4; // [bit]; do not change
  localparam int unsigned DMA_MAX_BURST_SIZE = 2048; // [B], must be a power of 2
  // Maximum number of beats in a DMA burst on the SoC bus
  localparam int unsigned DMA_MAX_BURST_LEN = DMA_MAX_BURST_SIZE / (AXI_DW/8);
  // Maximum number of transactions the DMA can have in flight
  localparam int unsigned DMA_MAX_N_TXNS = N_CORES;
  localparam int unsigned N_DMAS = 4; // larger values seem to break the cluster
  // -- Instruction Cache
  localparam int unsigned ICACHE_SIZE = 4096; // [B], must be a power of 2
  localparam int unsigned AXI_DW_ICACHE = 64; // [bit]; do not change, seems to break instruction cache
  localparam int unsigned AXI_IW_ICACHE = 6; // [bit]; do not change, seems to break instruction cache
  // -- TCDM
  localparam int unsigned N_TCDM_BANKS = 8*N_CORES; // must be a power of 2
  localparam int unsigned TCDM_SIZE = 1024*1024; // [B], must be a power of 2
  localparam int unsigned TCDM_WORDS_PER_BANK = (TCDM_SIZE / 4) / N_TCDM_BANKS;
  // -- L2 Memory (not inside cluster)
  localparam int unsigned L2_SIZE = 8192*1024; // [B], must be a power of 2

  typedef logic          [AXI_AW-1:0] addr_t;
  typedef logic                 [5:0] cluster_id_t;
  typedef logic          [AXI_DW-1:0] data_t;
  typedef logic      [AXI_DMA_DW-1:0] data_dma_t;
  typedef logic   [AXI_DW_ICACHE-1:0] data_icache_t;
  typedef logic        [DC_BUF_W-1:0] dc_buf_t;
  typedef logic      [AXI_IW_MST-1:0] id_mst_t;
  typedef logic      [AXI_IW_SLV-1:0] id_slv_t;
  typedef logic      [AXI_DMA_IW-1:0] id_dma_t;
  typedef logic   [AXI_IW_ICACHE-1:0] id_icache_t;
  typedef logic        [AXI_DW/8-1:0] strb_t;
  typedef logic    [AXI_DMA_DW/8-1:0] strb_dma_t;
  typedef logic [AXI_DW_ICACHE/8-1:0] strb_icache_t;
  typedef logic          [AXI_UW-1:0] user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_mst_t, addr_t, id_mst_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(aw_slv_t, addr_t, id_slv_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(aw_dma_t, addr_t, id_dma_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(aw_icache_t, addr_t, id_icache_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_dma_t, data_dma_t, strb_dma_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_icache_t, data_icache_t, strb_icache_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_mst_t, id_mst_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_slv_t, id_slv_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_dma_t, id_dma_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_icache_t, id_icache_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_mst_t, addr_t, id_mst_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_slv_t, addr_t, id_slv_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_dma_t, addr_t, id_dma_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_icache_t, addr_t, id_icache_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_mst_t, data_t, id_mst_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_slv_t, data_t, id_slv_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_dma_t, data_dma_t, id_dma_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_icache_t, data_icache_t, id_icache_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_mst_t, aw_mst_t, w_t, ar_mst_t)
  `AXI_TYPEDEF_REQ_T(req_slv_t, aw_slv_t, w_t, ar_slv_t)
  `AXI_TYPEDEF_REQ_T(req_dma_t, aw_dma_t, w_dma_t, ar_dma_t)
  `AXI_TYPEDEF_REQ_T(req_icache_t, aw_icache_t, w_icache_t, ar_icache_t)
  `AXI_TYPEDEF_RESP_T(resp_mst_t, b_mst_t, r_mst_t)
  `AXI_TYPEDEF_RESP_T(resp_slv_t, b_slv_t, r_slv_t)
  `AXI_TYPEDEF_RESP_T(resp_dma_t, b_dma_t, r_dma_t)
  `AXI_TYPEDEF_RESP_T(resp_icache_t, b_icache_t, r_icache_t)
endpackage
