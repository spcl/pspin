// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/*
 * pulp_cluster.sv
 * Davide Rossi <davide.rossi@unibo.it>
 * Antonio Pullini <pullinia@iis.ee.ethz.ch>
 * Igor Loi <igor.loi@unibo.it>
 * Francesco Conti <fconti@iis.ee.ethz.ch>
 * Thomas Benz <tbenz@iis.ee.ethz.ch>
 */

import pulp_cluster_package::*;
import apu_package::*;

`include "axi/assign.svh"
`include "axi/typedef.svh"

module pulp_cluster
#(
  // cluster parameters
  parameter bit ASYNC_INTF          = 1'b1,
  parameter int NB_CORES            = 8,
  parameter int NB_HWACC_PORTS      = 0,
  parameter int NB_DMAS             = 4,
  parameter int NB_EXT2MEM          = 2,
  parameter int NB_MPERIPHS         = 1,
  parameter int NB_SPERIPHS         = 8,
  parameter bit CLUSTER_ALIAS       = 1'b1,
  parameter int CLUSTER_ALIAS_BASE  = 12'h1B0,
  parameter int TCDM_SIZE           = 256*1024,                // [B], must be 2**N
  parameter int NB_TCDM_BANKS       = 16,                      // must be 2**N
  parameter int TCDM_BANK_SIZE      = TCDM_SIZE/NB_TCDM_BANKS, // [B]
  parameter int TCDM_NUM_ROWS       = TCDM_BANK_SIZE/4,        // [words]
  parameter bit XNE_PRESENT         = 0,                       // set to 1 if XNE is present in the cluster

  // I$ parameters
  parameter int SET_ASSOCIATIVE           = 4,
  parameter int NB_CACHE_BANKS            = 4,
  parameter int CACHE_LINE                = 1,
  parameter int CACHE_SIZE                = 4096,
  parameter int ICACHE_DATA_WIDTH         = 128,
  parameter int L2_SIZE                   = 256*1024,
  parameter bit USE_REDUCED_TAG           = 1'b1,

  // core parameters
  parameter bit DEM_PER_BEFORE_TCDM_TS  = 1'b0,
  parameter int ROM_BOOT_ADDR           = 32'h1A000000,
  parameter int BOOT_ADDR               = 32'h1C000000,
  parameter int INSTR_RDATA_WIDTH       = 128,

  // AXI parameters
  parameter int AXI_ADDR_WIDTH        = 32,
  parameter int AXI_DATA_C2S_WIDTH    = 64,
  parameter int AXI_DATA_S2C_WIDTH    = 64,
  parameter int AXI_USER_WIDTH        = 6,
  parameter int AXI_ID_IN_WIDTH       = 4,
  parameter int AXI_ID_OUT_WIDTH      = 6,
  parameter int AXI_STRB_C2S_WIDTH    = AXI_DATA_C2S_WIDTH/8,
  parameter int AXI_STRB_S2C_WIDTH    = AXI_DATA_S2C_WIDTH/8,
  parameter int DC_SLICE_BUFFER_WIDTH = 8,

  // TCDM and log interconnect parameters
  parameter int DATA_WIDTH      = 32,
  parameter int ADDR_WIDTH      = 32,
  parameter int BE_WIDTH        = DATA_WIDTH/8,
  parameter int TEST_SET_BIT    = 20,                       // bit used to indicate a test-and-set operation during a load in TCDM
  parameter int ADDR_MEM_WIDTH  = $clog2(TCDM_BANK_SIZE/4), // WORD address width per TCDM bank (the word width is 32 bits)

  // DMA parameters
  parameter int TCDM_ADD_WIDTH      = ADDR_MEM_WIDTH + $clog2(NB_TCDM_BANKS) + 2, // BYTE address width TCDM
  parameter int NB_OUTSND_BURSTS    = 8,
  parameter int MCHAN_BURST_LENGTH  = 256,

  // peripheral and periph interconnect parameters
  parameter int LOG_CLUSTER     = 5,  // unused
  parameter int PE_ROUTING_LSB  = 10, // LSB used as routing BIT in periph interco
  parameter int PE_ROUTING_MSB  = 13, // MSB used as routing BIT in periph interco
  parameter int EVNT_WIDTH      = 8,  // size of the event bus
  parameter int REMAP_ADDRESS   = 0,  // for cluster virtualization

  // WIDE DMA parameters
  parameter int DMA_AXI_ID_WIDTH = 4,  //
  parameter int DMA_AXI_AW_WIDTH = 32, // DON'T CHANGE
  parameter int DMA_AXI_DW_WIDTH = 512,// DON'T CHANGE
  parameter int DMA_AXI_UW_WIDTH = 4   //
)
(
  input  logic                             clk_i,
  input  logic                             rst_ni,
  input  logic                             ref_clk_i,
  input  logic                             pmu_mem_pwdn_i,

  input logic [3:0]                        base_addr_i,

  input logic                              test_mode_i,

  input logic                              en_sa_boot_i,

  input logic [5:0]                        cluster_id_i,

  input logic                              fetch_en_i,

  output logic                             eoc_o,

  output logic                             busy_o,

  input  logic [DC_SLICE_BUFFER_WIDTH-1:0] ext_events_writetoken_i,
  output logic [DC_SLICE_BUFFER_WIDTH-1:0] ext_events_readpointer_o,
  input  logic            [EVNT_WIDTH-1:0] ext_events_dataasync_i,

  input  logic                             dma_pe_evt_ack_i,
  output logic                             dma_pe_evt_valid_o,

  input  logic                             dma_pe_irq_ack_i,
  output logic                             dma_pe_irq_valid_o,

  input  logic                             pf_evt_ack_i,
  output logic                             pf_evt_valid_o,

  // AXI4 SLAVE
  //***************************************
  // WRITE ADDRESS CHANNEL
  input  logic [AXI_ADDR_WIDTH-1:0]        data_slave_aw_addr_i,
  input  axi_pkg::prot_t                   data_slave_aw_prot_i,
  input  axi_pkg::region_t                 data_slave_aw_region_i,
  input  axi_pkg::len_t                    data_slave_aw_len_i,
  input  axi_pkg::size_t                   data_slave_aw_size_i,
  input  axi_pkg::burst_t                  data_slave_aw_burst_i,
  input  logic                             data_slave_aw_lock_i,
  input  axi_pkg::atop_t                   data_slave_aw_atop_i,
  input  axi_pkg::cache_t                  data_slave_aw_cache_i,
  input  axi_pkg::qos_t                    data_slave_aw_qos_i,
  input  logic [AXI_ID_IN_WIDTH-1:0]       data_slave_aw_id_i,
  input  logic [AXI_USER_WIDTH-1:0]        data_slave_aw_user_i,
  // used if ASYNC_INTF
  input  logic [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_aw_writetoken_i,
  output logic [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_aw_readpointer_o,
  // used if !ASYNC_INTF
  input  logic                             data_slave_aw_valid_i,
  output logic                             data_slave_aw_ready_o,

  // READ ADDRESS CHANNEL
  input  logic [AXI_ADDR_WIDTH-1:0]        data_slave_ar_addr_i,
  input  axi_pkg::prot_t                   data_slave_ar_prot_i,
  input  axi_pkg::region_t                 data_slave_ar_region_i,
  input  axi_pkg::len_t                    data_slave_ar_len_i,
  input  axi_pkg::size_t                   data_slave_ar_size_i,
  input  axi_pkg::burst_t                  data_slave_ar_burst_i,
  input  logic                             data_slave_ar_lock_i,
  input  axi_pkg::cache_t                  data_slave_ar_cache_i,
  input  axi_pkg::qos_t                    data_slave_ar_qos_i,
  input  logic [AXI_ID_IN_WIDTH-1:0]       data_slave_ar_id_i,
  input  logic [AXI_USER_WIDTH-1:0]        data_slave_ar_user_i,
  // used if ASYNC_INTF
  input  logic [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_ar_writetoken_i,
  output logic [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_ar_readpointer_o,
  // used if !ASYNC_INTF
  input  logic                             data_slave_ar_valid_i,
  output logic                             data_slave_ar_ready_o,

  // WRITE DATA CHANNEL
  input  logic [AXI_DATA_S2C_WIDTH-1:0]    data_slave_w_data_i,
  input  logic [AXI_STRB_S2C_WIDTH-1:0]    data_slave_w_strb_i,
  input  logic [AXI_USER_WIDTH-1:0]        data_slave_w_user_i,
  input  logic                             data_slave_w_last_i,
  // used if ASYNC_INTF
  input  logic [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_w_writetoken_i,
  output logic [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_w_readpointer_o,
  // used if !ASYNC_INTF
  input  logic                             data_slave_w_valid_i,
  output logic                             data_slave_w_ready_o,

  // READ DATA CHANNEL
  output logic [AXI_DATA_S2C_WIDTH-1:0]    data_slave_r_data_o,
  output axi_pkg::resp_t                   data_slave_r_resp_o,
  output logic                             data_slave_r_last_o,
  output logic [AXI_ID_IN_WIDTH-1:0]       data_slave_r_id_o,
  output logic [AXI_USER_WIDTH-1:0]        data_slave_r_user_o,
  // used if ASYNC_INTF
  output logic [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_r_writetoken_o,
  input  logic [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_r_readpointer_i,
  // used if !ASYNC_INTF
  output logic                             data_slave_r_valid_o,
  input  logic                             data_slave_r_ready_i,

  // WRITE RESPONSE CHANNEL
  output axi_pkg::resp_t                   data_slave_b_resp_o,
  output logic [AXI_ID_IN_WIDTH-1:0]       data_slave_b_id_o,
  output logic [AXI_USER_WIDTH-1:0]        data_slave_b_user_o,
  // used if ASYNC_INTF
  output logic [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_b_writetoken_o,
  input  logic [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_b_readpointer_i,
  // used if !ASYNC_INTF
  output logic                             data_slave_b_valid_o,
  input  logic                             data_slave_b_ready_i,

  // AXI4 MASTER
  //***************************************
  // WRITE ADDRESS CHANNEL
  output logic [AXI_ADDR_WIDTH-1:0]        data_master_aw_addr_o,
  output axi_pkg::prot_t                   data_master_aw_prot_o,
  output axi_pkg::region_t                 data_master_aw_region_o,
  output axi_pkg::len_t                    data_master_aw_len_o,
  output axi_pkg::size_t                   data_master_aw_size_o,
  output axi_pkg::burst_t                  data_master_aw_burst_o,
  output logic                             data_master_aw_lock_o,
  output axi_pkg::atop_t                   data_master_aw_atop_o,
  output axi_pkg::cache_t                  data_master_aw_cache_o,
  output axi_pkg::qos_t                    data_master_aw_qos_o,
  output logic [AXI_ID_OUT_WIDTH-1:0]      data_master_aw_id_o,
  output logic [AXI_USER_WIDTH-1:0]        data_master_aw_user_o,
  // used if ASYNC_INTF
  output logic [DC_SLICE_BUFFER_WIDTH-1:0] data_master_aw_writetoken_o,
  input  logic [DC_SLICE_BUFFER_WIDTH-1:0] data_master_aw_readpointer_i,
  // used if !ASYNC_INTF
  output logic                             data_master_aw_valid_o,
  input  logic                             data_master_aw_ready_i,

  // READ ADDRESS CHANNEL
  output logic [AXI_ADDR_WIDTH-1:0]        data_master_ar_addr_o,
  output axi_pkg::prot_t                   data_master_ar_prot_o,
  output axi_pkg::region_t                 data_master_ar_region_o,
  output axi_pkg::len_t                    data_master_ar_len_o,
  output axi_pkg::size_t                   data_master_ar_size_o,
  output axi_pkg::burst_t                  data_master_ar_burst_o,
  output logic                             data_master_ar_lock_o,
  output axi_pkg::cache_t                  data_master_ar_cache_o,
  output axi_pkg::qos_t                    data_master_ar_qos_o,
  output logic [AXI_ID_OUT_WIDTH-1:0]      data_master_ar_id_o,
  output logic [AXI_USER_WIDTH-1:0]        data_master_ar_user_o,
  // used if ASYNC_INTF
  output logic [DC_SLICE_BUFFER_WIDTH-1:0] data_master_ar_writetoken_o,
  input  logic [DC_SLICE_BUFFER_WIDTH-1:0] data_master_ar_readpointer_i,
  // used if !ASYNC_INTF
  output logic                             data_master_ar_valid_o,
  input  logic                             data_master_ar_ready_i,

  // WRITE DATA CHANNEL
  output logic [AXI_DATA_C2S_WIDTH-1:0]    data_master_w_data_o,
  output logic [AXI_STRB_C2S_WIDTH-1:0]    data_master_w_strb_o,
  output logic [AXI_USER_WIDTH-1:0]        data_master_w_user_o,
  output logic                             data_master_w_last_o,
  // used if ASYNC_INTF
  output logic [DC_SLICE_BUFFER_WIDTH-1:0] data_master_w_writetoken_o,
  input  logic [DC_SLICE_BUFFER_WIDTH-1:0] data_master_w_readpointer_i,
  // used if !ASYNC_INTF
  output logic                             data_master_w_valid_o,
  input  logic                             data_master_w_ready_i,

  // READ DATA CHANNEL
  input  logic [AXI_DATA_C2S_WIDTH-1:0]    data_master_r_data_i,
  input  axi_pkg::resp_t                   data_master_r_resp_i,
  input  logic                             data_master_r_last_i,
  input  logic [AXI_ID_OUT_WIDTH-1:0]      data_master_r_id_i,
  input  logic [AXI_USER_WIDTH-1:0]        data_master_r_user_i,
  // used if ASYNC_INTF
  input  logic [DC_SLICE_BUFFER_WIDTH-1:0] data_master_r_writetoken_i,
  output logic [DC_SLICE_BUFFER_WIDTH-1:0] data_master_r_readpointer_o,
  // used if !ASYNC_INTF
  input  logic                             data_master_r_valid_i,
  output logic                             data_master_r_ready_o,

  // WRITE RESPONSE CHANNEL
  input  axi_pkg::resp_t                   data_master_b_resp_i,
  input  logic [AXI_ID_OUT_WIDTH-1:0]      data_master_b_id_i,
  input  logic [AXI_USER_WIDTH-1:0]        data_master_b_user_i,
  // used if ASYNC_INTF
  input  logic [DC_SLICE_BUFFER_WIDTH-1:0] data_master_b_writetoken_i,
  output logic [DC_SLICE_BUFFER_WIDTH-1:0] data_master_b_readpointer_o,
  // used if !ASYNC_INTF
  input  logic                             data_master_b_valid_i,
  output logic                             data_master_b_ready_o,

  // AXI4 DMA MASTER
  //***************************************
  // WRITE ADDRESS CHANNEL
  output logic [DMA_AXI_AW_WIDTH-1:0]      dma_aw_addr_o,
  output axi_pkg::prot_t                   dma_aw_prot_o,
  output axi_pkg::region_t                 dma_aw_region_o,
  output axi_pkg::len_t                    dma_aw_len_o,
  output axi_pkg::size_t                   dma_aw_size_o,
  output axi_pkg::burst_t                  dma_aw_burst_o,
  output logic                             dma_aw_lock_o,
  output axi_pkg::atop_t                   dma_aw_atop_o,
  output axi_pkg::cache_t                  dma_aw_cache_o,
  output axi_pkg::qos_t                    dma_aw_qos_o,
  output logic [DMA_AXI_ID_WIDTH-1:0]      dma_aw_id_o,
  output logic [DMA_AXI_UW_WIDTH-1:0]      dma_aw_user_o,
  output logic                             dma_aw_valid_o,
  input  logic                             dma_aw_ready_i,

  // READ ADDRESS CHANNEL
  output logic [DMA_AXI_AW_WIDTH-1:0]      dma_ar_addr_o,
  output axi_pkg::prot_t                   dma_ar_prot_o,
  output axi_pkg::region_t                 dma_ar_region_o,
  output axi_pkg::len_t                    dma_ar_len_o,
  output axi_pkg::size_t                   dma_ar_size_o,
  output axi_pkg::burst_t                  dma_ar_burst_o,
  output logic                             dma_ar_lock_o,
  output axi_pkg::cache_t                  dma_ar_cache_o,
  output axi_pkg::qos_t                    dma_ar_qos_o,
  output logic [DMA_AXI_ID_WIDTH-1:0]      dma_ar_id_o,
  output logic [DMA_AXI_UW_WIDTH-1:0]      dma_ar_user_o,
  output logic                             dma_ar_valid_o,
  input  logic                             dma_ar_ready_i,

  // WRITE DATA CHANNEL
  output logic [DMA_AXI_DW_WIDTH-1:0]      dma_w_data_o,
  output logic [DMA_AXI_DW_WIDTH/8-1:0]    dma_w_strb_o,
  output logic [DMA_AXI_UW_WIDTH-1:0]      dma_w_user_o,
  output logic                             dma_w_last_o,
  output logic                             dma_w_valid_o,
  input  logic                             dma_w_ready_i,

  // READ DATA CHANNEL
  input  logic [DMA_AXI_DW_WIDTH-1:0]      dma_r_data_i,
  input  axi_pkg::resp_t                   dma_r_resp_i,
  input  logic                             dma_r_last_i,
  input  logic [DMA_AXI_ID_WIDTH-1:0]      dma_r_id_i,
  input  logic [DMA_AXI_UW_WIDTH-1:0]      dma_r_user_i,
  input  logic                             dma_r_valid_i,
  output logic                             dma_r_ready_o,

  // WRITE RESPONSE CHANNEL
  input  axi_pkg::resp_t                   dma_b_resp_i,
  input  logic [DMA_AXI_ID_WIDTH-1:0]      dma_b_id_i,
  input  logic [DMA_AXI_UW_WIDTH-1:0]      dma_b_user_i,
  input  logic                             dma_b_valid_i,
  output logic                             dma_b_ready_o,

  // AXI4 NIC-HOST-Interconnect (NHI) SLAVE
  //***************************************
  // WRITE ADDRESS CHANNEL
  input  logic [DMA_AXI_AW_WIDTH-1:0]      nhi_aw_addr_i,
  input  axi_pkg::prot_t                   nhi_aw_prot_i,
  input  axi_pkg::region_t                 nhi_aw_region_i,
  input  axi_pkg::len_t                    nhi_aw_len_i,
  input  axi_pkg::size_t                   nhi_aw_size_i,
  input  axi_pkg::burst_t                  nhi_aw_burst_i,
  input  logic                             nhi_aw_lock_i,
  input  axi_pkg::atop_t                   nhi_aw_atop_i,
  input  axi_pkg::cache_t                  nhi_aw_cache_i,
  input  axi_pkg::qos_t                    nhi_aw_qos_i,
  input  logic [DMA_AXI_ID_WIDTH-1:0]      nhi_aw_id_i,
  input  logic [DMA_AXI_UW_WIDTH-1:0]      nhi_aw_user_i,
  input  logic                             nhi_aw_valid_i,
  output logic                             nhi_aw_ready_o,

  // READ ADDRESS CHANNEL
  input  logic [DMA_AXI_AW_WIDTH-1:0]      nhi_ar_addr_i,
  input  axi_pkg::prot_t                   nhi_ar_prot_i,
  input  axi_pkg::region_t                 nhi_ar_region_i,
  input  axi_pkg::len_t                    nhi_ar_len_i,
  input  axi_pkg::size_t                   nhi_ar_size_i,
  input  axi_pkg::burst_t                  nhi_ar_burst_i,
  input  logic                             nhi_ar_lock_i,
  input  axi_pkg::cache_t                  nhi_ar_cache_i,
  input  axi_pkg::qos_t                    nhi_ar_qos_i,
  input  logic [DMA_AXI_ID_WIDTH-1:0]      nhi_ar_id_i,
  input  logic [DMA_AXI_UW_WIDTH-1:0]      nhi_ar_user_i,
  input  logic                             nhi_ar_valid_i,
  output logic                             nhi_ar_ready_o,

  // WRITE DATA CHANNEL
  input  logic [DMA_AXI_DW_WIDTH-1:0]      nhi_w_data_i,
  input  logic [DMA_AXI_DW_WIDTH/8-1:0]    nhi_w_strb_i,
  input  logic [DMA_AXI_UW_WIDTH-1:0]      nhi_w_user_i,
  input  logic                             nhi_w_last_i,
  input  logic                             nhi_w_valid_i,
  output logic                             nhi_w_ready_o,

  // READ DATA CHANNEL
  output logic [DMA_AXI_DW_WIDTH-1:0]      nhi_r_data_o,
  output axi_pkg::resp_t                   nhi_r_resp_o,
  output logic                             nhi_r_last_o,
  output logic [DMA_AXI_ID_WIDTH-1:0]      nhi_r_id_o,
  output logic [DMA_AXI_UW_WIDTH-1:0]      nhi_r_user_o,
  output logic                             nhi_r_valid_o,
  input  logic                             nhi_r_ready_i,

  // WRITE RESPONSE CHANNEL
  output axi_pkg::resp_t                   nhi_b_resp_o,
  output logic [DMA_AXI_ID_WIDTH-1:0]      nhi_b_id_o,
  output logic [DMA_AXI_UW_WIDTH-1:0]      nhi_b_user_o,
  output logic                             nhi_b_valid_o,
  input  logic                             nhi_b_ready_i,

  // Instruction Cache Master Port
  output pulp_cluster_cfg_pkg::addr_t         icache_aw_addr_o,
  output axi_pkg::prot_t                      icache_aw_prot_o,
  output axi_pkg::region_t                    icache_aw_region_o,
  output axi_pkg::len_t                       icache_aw_len_o,
  output axi_pkg::size_t                      icache_aw_size_o,
  output axi_pkg::burst_t                     icache_aw_burst_o,
  output logic                                icache_aw_lock_o,
  output axi_pkg::atop_t                      icache_aw_atop_o,
  output axi_pkg::cache_t                     icache_aw_cache_o,
  output axi_pkg::qos_t                       icache_aw_qos_o,
  output pulp_cluster_cfg_pkg::id_icache_t    icache_aw_id_o,
  output pulp_cluster_cfg_pkg::user_t         icache_aw_user_o,
  output logic                                icache_aw_valid_o,
  input  logic                                icache_aw_ready_i,

  output pulp_cluster_cfg_pkg::addr_t         icache_ar_addr_o,
  output axi_pkg::prot_t                      icache_ar_prot_o,
  output axi_pkg::region_t                    icache_ar_region_o,
  output axi_pkg::len_t                       icache_ar_len_o,
  output axi_pkg::size_t                      icache_ar_size_o,
  output axi_pkg::burst_t                     icache_ar_burst_o,
  output logic                                icache_ar_lock_o,
  output axi_pkg::cache_t                     icache_ar_cache_o,
  output axi_pkg::qos_t                       icache_ar_qos_o,
  output pulp_cluster_cfg_pkg::id_icache_t    icache_ar_id_o,
  output pulp_cluster_cfg_pkg::user_t         icache_ar_user_o,
  output logic                                icache_ar_valid_o,
  input  logic                                icache_ar_ready_i,

  output pulp_cluster_cfg_pkg::data_icache_t  icache_w_data_o,
  output pulp_cluster_cfg_pkg::strb_icache_t  icache_w_strb_o,
  output pulp_cluster_cfg_pkg::user_t         icache_w_user_o,
  output logic                                icache_w_last_o,
  output logic                                icache_w_valid_o,
  input  logic                                icache_w_ready_i,

  input  pulp_cluster_cfg_pkg::data_icache_t  icache_r_data_i,
  input  axi_pkg::resp_t                      icache_r_resp_i,
  input  logic                                icache_r_last_i,
  input  pulp_cluster_cfg_pkg::id_icache_t    icache_r_id_i,
  input  pulp_cluster_cfg_pkg::user_t         icache_r_user_i,
  input  logic                                icache_r_valid_i,
  output logic                                icache_r_ready_o,

  input  axi_pkg::resp_t                      icache_b_resp_i,
  input  pulp_cluster_cfg_pkg::id_icache_t    icache_b_id_i,
  input  pulp_cluster_cfg_pkg::user_t         icache_b_user_i,
  input  logic                                icache_b_valid_i,
  output logic                                icache_b_ready_o,

  //task from scheduler
  input  logic                                task_valid_i,
  output logic                                task_ready_o,
  input  pspin_cfg_pkg::handler_task_t            task_descr_i,

  //feedback to scheduler
  output logic                                feedback_valid_o,
  input  logic                                feedback_ready_i,
  output pspin_cfg_pkg::feedback_descr_t          feedback_o,

  //signal if the cluster is ready to accept tasks
  output logic                                cluster_active_o,

  //commands out
  input  logic                                cmd_ready_i,
  output logic                                cmd_valid_o,
  output pspin_cfg_pkg::pspin_cmd_t               cmd_o,

  //command response
  input  logic                                cmd_resp_valid_i,
  input  pspin_cfg_pkg::pspin_cmd_resp_t          cmd_resp_i
);

  logic [NB_CORES-1:0]                fetch_enable_reg_int;
  logic [NB_CORES-1:0]                fetch_en_int;
  logic                               s_rst_n;
  logic                               s_init_n;
  logic [NB_CORES-1:0][31:0]          boot_addr;
  logic [NB_CORES-1:0]                dbg_core_halt;
  logic [NB_CORES-1:0]                dbg_core_resume;
  logic [NB_CORES-1:0]                dbg_core_halted;
  logic                               hwpe_sel;
  logic                               hwpe_en;

  logic [NB_CORES-1:0][AXI_USER_WIDTH-1:0] tryx_axuser;
  logic [NB_CORES-1:0]                     tryx_xresp_decerr;
  logic [NB_CORES-1:0]                     tryx_xresp_slverr;
  logic [NB_CORES-1:0]                     tryx_xresp_valid;

  logic                s_cluster_periphs_busy;
  logic                s_axi_to_mem_busy;
  logic                s_per2axi_busy;
  logic                s_axi2per_busy;
  logic                s_dmac_busy;
  logic                s_cluster_cg_en;
  logic [NB_CORES-1:0] s_dma_event;
  logic [NB_CORES-1:0] s_dma_irq;
  logic [NB_CORES-1:0][3:0]  s_hwacc_events;
  logic [NB_CORES-1:0][1:0]  s_xne_evt;
  logic                      s_xne_busy;

  logic [NB_CORES-1:0]               clk_core_en;
  logic                              clk_cluster;

  // CLK reset, and other control signals

  logic                              s_cluster_int_busy;
  logic                              s_fregfile_disable;

  logic [NB_CORES-1:0]               core_busy;

  logic                              s_incoming_req;
  logic                              s_isolate_cluster;
  logic                              s_events_async;

  logic                              s_events_valid;
  logic                              s_events_ready;
  logic [EVNT_WIDTH-1:0]             s_events_data;

  // Signals Between CORE_ISLAND and INSTRUCTION CACHES
  logic [NB_CORES-1:0]                        instr_req;
  logic [NB_CORES-1:0][31:0]                  instr_addr;
  logic [NB_CORES-1:0]                        instr_gnt;
  logic [NB_CORES-1:0]                        instr_r_valid;
  logic [NB_CORES-1:0][INSTR_RDATA_WIDTH-1:0] instr_r_rdata;

  logic [1:0]                                 s_TCDM_arb_policy;
  logic                                       tcdm_sleep;

  logic               s_dma_pe_event;
  logic               s_dma_pe_irq;
  logic               s_pf_event;

  logic[NB_CORES-1:0][4:0] irq_id;
  logic[NB_CORES-1:0][4:0] irq_ack_id;
  logic[NB_CORES-1:0]      irq_req;
  logic[NB_CORES-1:0]      irq_ack;


  /* asynchronous AXI interfaces at CLUSTER/SOC interface, driven iff `ASYNC_INTF` */
  AXI_BUS_ASYNC #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH        ),
    .AXI_DATA_WIDTH ( AXI_DATA_S2C_WIDTH    ),
    .AXI_ID_WIDTH   ( AXI_ID_IN_WIDTH       ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH        ),
    .BUFFER_WIDTH   ( DC_SLICE_BUFFER_WIDTH )
  ) s_data_slave_async();

  AXI_BUS_ASYNC #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH        ),
    .AXI_DATA_WIDTH ( AXI_DATA_C2S_WIDTH    ),
    .AXI_ID_WIDTH   ( AXI_ID_OUT_WIDTH      ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH        ),
    .BUFFER_WIDTH   ( DC_SLICE_BUFFER_WIDTH )
  ) s_data_master_async();

  /* synchronously cut (no combinatorial paths) AXI interfaces, driven iff `!ASYNC_INTF` */
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH     ),
    .AXI_DATA_WIDTH ( AXI_DATA_S2C_WIDTH ),
    .AXI_ID_WIDTH   ( AXI_ID_IN_WIDTH    ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH     )
  ) s_data_slave_cut();

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH     ),
    .AXI_DATA_WIDTH ( AXI_DATA_C2S_WIDTH ),
    .AXI_ID_WIDTH   ( AXI_ID_OUT_WIDTH   ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH     )
  ) s_data_master_cut();

  /* synchronous AXI interfaces at CLUSTER/SOC interface */
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH     ),
    .AXI_DATA_WIDTH ( AXI_DATA_S2C_WIDTH ),
    .AXI_ID_WIDTH   ( AXI_ID_IN_WIDTH    ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH     )
  ) s_data_slave();

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH     ),
    .AXI_DATA_WIDTH ( AXI_DATA_C2S_WIDTH ),
    .AXI_ID_WIDTH   ( AXI_ID_OUT_WIDTH   ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH     )
  ) s_data_master();

  /* synchronous AXI interfaces internal to the cluster */
  // core per2axi -> ext
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH     ),
    .AXI_DATA_WIDTH ( AXI_DATA_C2S_WIDTH ),
    .AXI_ID_WIDTH   ( AXI_ID_IN_WIDTH    ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH     )
  ) s_core_ext_bus();

  // DMA -> ext
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH     ),
    .AXI_DATA_WIDTH ( AXI_DATA_C2S_WIDTH ),
    .AXI_ID_WIDTH   ( AXI_ID_IN_WIDTH    ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH     )
  ) s_dma_ext_bus();

  // WIDE DMA -> SoC
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( DMA_AXI_AW_WIDTH     ),
    .AXI_DATA_WIDTH ( DMA_AXI_DW_WIDTH     ),
    .AXI_ID_WIDTH   ( DMA_AXI_ID_WIDTH     ),
    .AXI_USER_WIDTH ( DMA_AXI_UW_WIDTH     )
  ) s_wide_dma_soc();

  // WIDE NHI -> TCDM (supprbanks)
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( DMA_AXI_AW_WIDTH     ),
    .AXI_DATA_WIDTH ( DMA_AXI_DW_WIDTH     ),
    .AXI_ID_WIDTH   ( DMA_AXI_ID_WIDTH     ),
    .AXI_USER_WIDTH ( DMA_AXI_UW_WIDTH     )
  ) s_wide_nhi_superbanks();

  // ext -> axi_to_mem
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH     ),
    .AXI_DATA_WIDTH ( AXI_DATA_C2S_WIDTH ),
    .AXI_ID_WIDTH   ( AXI_ID_OUT_WIDTH   ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH     )
  ) s_ext_tcdm_bus();

  // cluster bus -> axi2per
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH     ),
    .AXI_DATA_WIDTH ( AXI_DATA_C2S_WIDTH ),
    .AXI_ID_WIDTH   ( AXI_ID_OUT_WIDTH   ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH     )
  ) s_ext_mperiph_bus();

  /* logarithmic and peripheral interconnect interfaces */
  // wide dma -> superbanks a
  WIDE_DMA_TCDM_BUS #(
    .ADDR_WIDTH ( DMA_AXI_AW_WIDTH ),
    .DATA_WIDTH ( DMA_AXI_DW_WIDTH )
  ) s_wide_dma_a_superbanks();

  // NHI interconnect -> superbanks b
  WIDE_DMA_TCDM_BUS #(
    .ADDR_WIDTH ( DMA_AXI_AW_WIDTH ),
    .DATA_WIDTH ( DMA_AXI_DW_WIDTH )
  ) s_wide_dma_b_superbanks();


  // ext -> log interconnect
  XBAR_TCDM_BUS s_ext_xbar_bus[NB_EXT2MEM-1:0]();

  // periph interconnect -> slave peripherals
  XBAR_PERIPH_BUS s_xbar_speriph_bus[NB_SPERIPHS-1:0]();
  logic [NB_SPERIPHS-1:0][5:0] s_xbar_speriph_atop;

  // periph interconnect -> XNE
  XBAR_PERIPH_BUS s_xne_cfg_bus();

  // DMA -> log interconnect
  XBAR_TCDM_BUS s_dma_xbar_bus[NB_DMAS-1:0]();

  // ext -> xbar periphs FIXME
  XBAR_TCDM_BUS s_mperiph_xbar_bus[NB_MPERIPHS-1:0]();

  // periph demux
  XBAR_TCDM_BUS s_mperiph_bus();
  XBAR_TCDM_BUS s_mperiph_demux_bus[1:0]();

  // cores & accelerators -> log interconnect
  XBAR_TCDM_BUS s_core_xbar_bus[NB_CORES+NB_HWACC_PORTS-1:0]();

  // cores -> periph interconnect
  XBAR_PERIPH_BUS s_core_periph_bus[NB_CORES-1:0]();
  XBAR_PERIPH_BUS s_inter_core_fifo[NB_CORES-1:0]();
  XBAR_PERIPH_BUS s_hpu_driver_bus[NB_CORES-1:0]();
  logic [NB_CORES-1:0][5:0] s_core_periph_bus_atop, s_core_xbar_bus_atop;

  // cores -> tryx control
  XBAR_PERIPH_BUS s_core_periph_tryx[NB_CORES-1:0]();

  // periph interconnect -> DMA
  XBAR_PERIPH_BUS s_periph_dma_bus();

  // debug
  XBAR_TCDM_BUS s_debug_bus[NB_CORES-1:0]();

  /* other interfaces */
  // cores -> DMA ctrl
  XBAR_TCDM_BUS s_core_dmactrl_bus[NB_CORES-1:0]();

  // cores -> event unit ctrl
  XBAR_PERIPH_BUS s_core_euctrl_bus[NB_CORES-1:0]();

  // I$ ctrl unit <-> I$, L0, I$ interconnect
  MP_PF_ICACHE_CTRL_UNIT_BUS  IC_ctrl_unit_bus();

  // log interconnect -> TCDM memory banks (SRAM)
  TCDM_BANK_MEM_BUS s_tcdm_bus_sram[NB_TCDM_BANKS-1:0]();

  // cluster_scheduler -> dma_wrap
  logic                     ext_dma_req_valid;
  logic                     ext_dma_req_ready;
  pspin_cfg_pkg::transf_descr_32_t ext_dma_req;

  // dma_wrap -> cluster_scheduler
  logic                     ext_dma_rsp_valid;

  // cluster_schedulers -> hpu_drivers
  logic [NB_CORES-1:0]                          hpu_task_valid;
  logic [NB_CORES-1:0]                          hpu_task_ready;
  pspin_cfg_pkg::hpu_handler_task_t                 hpu_task;

  // hpu_drivers -> cluster_schedulers
  logic [NB_CORES-1:0]                            hpu_feedback_valid;
  logic [NB_CORES-1:0]                            hpu_feedback_ready;
  pspin_cfg_pkg::task_feedback_descr_t [NB_CORES-1:0] hpu_feedback;

  logic [NB_CORES-1:0]                            hpu_active;

  logic [NB_CORES-1:0]                            core_cmd_ready;
  logic [NB_CORES-1:0]                            core_cmd_valid;
  pspin_cfg_pkg::pspin_cmd_t [NB_CORES-1:0]           core_cmd;

  // cores -> APU
  cpu_marx_if #(
    .WOP_CPU      ( WOP_CPU      ),
    .WAPUTYPE     ( WAPUTYPE     ),
    .NUSFLAGS_CPU ( NUSFLAGS_CPU ),
    .NDSFLAGS_CPU ( NDSFLAGS_CPU ),
    .NARGS_CPU    ( NARGS_CPU    )
  ) apu_cluster_bus [NB_CORES-1:0] ();

  /* reset generator */
  rstgen rstgen_i (
    .clk_i      ( clk_i       ),
    .rst_ni     ( rst_ni      ),
    .test_mode_i( test_mode_i ),
    .rst_no     ( s_rst_n     ),
    .init_no    ( s_init_n    )
  );

  /* fetch & busy genertion */
  assign s_cluster_int_busy = s_cluster_periphs_busy | s_per2axi_busy | s_axi2per_busy | s_axi_to_mem_busy | s_dmac_busy | s_xne_busy;
  assign busy_o = s_cluster_int_busy | (|core_busy);
  assign fetch_en_int = fetch_enable_reg_int;

  /* cluster bus and attached peripherals */
  cluster_bus_wrap #(
    .NB_CORES         ( NB_CORES           ),
    .AXI_ADDR_WIDTH   ( AXI_ADDR_WIDTH     ),
    .AXI_DATA_WIDTH   ( AXI_DATA_C2S_WIDTH ),
    .AXI_USER_WIDTH   ( AXI_USER_WIDTH     ),
    .AXI_ID_IN_WIDTH  ( AXI_ID_IN_WIDTH    ),
    .AXI_ID_OUT_WIDTH ( AXI_ID_OUT_WIDTH   )
  ) cluster_bus_wrap_i (
    .clk_i         ( clk_cluster       ),
    .rst_ni        ( rst_ni            ),
    .test_en_i     ( test_mode_i       ),
    .cluster_id_i  ( cluster_id_i      ),
    .data_slave    ( s_core_ext_bus    ),
    .dma_slave     ( s_dma_ext_bus     ),
    .ext_slave     ( s_data_slave      ),
    .tcdm_master   ( s_ext_tcdm_bus    ),
    .periph_master ( s_ext_mperiph_bus ),
    .ext_master    ( s_data_master     )
  );

  logic [NB_EXT2MEM-1:0]        s_ext_xbar_bus_req, s_ext_xbar_bus_gnt,
                                s_ext_xbar_bus_wen,
                                s_ext_xbar_bus_rvalid;
  logic [NB_EXT2MEM-1:0][31:0]  s_ext_xbar_bus_addr,
                                s_ext_xbar_bus_rdata,
                                s_ext_xbar_bus_wdata;
  logic [NB_EXT2MEM-1:0][ 3:0]  s_ext_xbar_bus_be;
  logic [NB_EXT2MEM-1:0][ 5:0]  s_ext_xbar_bus_atop;

  // Fall-through register on AW due to protocol violation by upstream (dependency on aw_ready for
  // w_valid).
  typedef logic [31:0] addr_t;
  typedef logic [AXI_DATA_C2S_WIDTH-1:0] data_t;
  typedef logic [AXI_ID_OUT_WIDTH-1:0] id_oup_t;
  typedef logic [AXI_DATA_C2S_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0] user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_oup_t, user_t);
  `AXI_TYPEDEF_W_CHAN_T (w_chan_t, data_t, strb_t, user_t);
  `AXI_TYPEDEF_B_CHAN_T (b_chan_t, id_oup_t, user_t);
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_oup_t, user_t);
  `AXI_TYPEDEF_R_CHAN_T (r_chan_t, data_t, id_oup_t, user_t);
  `AXI_TYPEDEF_REQ_T    (axi_req_t, aw_chan_t, w_chan_t, ar_chan_t);
  `AXI_TYPEDEF_RESP_T   (axi_resp_t, b_chan_t, r_chan_t);
  axi_req_t   ext_tcdm_req,   ext_tcdm_req_buf;
  axi_resp_t  ext_tcdm_resp,  ext_tcdm_resp_buf;
  `AXI_ASSIGN_TO_REQ(ext_tcdm_req, s_ext_tcdm_bus);
  `AXI_ASSIGN_FROM_RESP(s_ext_tcdm_bus, ext_tcdm_resp);
  always_comb begin
    ext_tcdm_req_buf.w = ext_tcdm_req.w;
    ext_tcdm_req_buf.w_valid = ext_tcdm_req.w_valid;
    ext_tcdm_resp.w_ready = ext_tcdm_resp_buf.w_ready;
    ext_tcdm_req_buf.ar = ext_tcdm_req.ar;
    ext_tcdm_req_buf.ar_valid = ext_tcdm_req.ar_valid;
    ext_tcdm_resp.ar_ready = ext_tcdm_resp_buf.ar_ready;
    ext_tcdm_resp.b = ext_tcdm_resp_buf.b;
    ext_tcdm_resp.b_valid = ext_tcdm_resp_buf.b_valid;
    ext_tcdm_req_buf.b_ready = ext_tcdm_req.b_ready;
    ext_tcdm_resp.r = ext_tcdm_resp_buf.r;
    ext_tcdm_resp.r_valid = ext_tcdm_resp_buf.r_valid;
    ext_tcdm_req_buf.r_ready = ext_tcdm_req.r_ready;
  end
  fall_through_register #(
    .T  (aw_chan_t)
  ) i_axi_to_mem_aw_ft_reg (
    .clk_i  (clk_cluster),
    .rst_ni,
    .clr_i  (1'b0),
    .testmode_i (1'b0),
    .valid_i  (ext_tcdm_req.aw_valid),
    .ready_o  (ext_tcdm_resp.aw_ready),
    .data_i   (ext_tcdm_req.aw),
    .valid_o  (ext_tcdm_req_buf.aw_valid),
    .ready_i  (ext_tcdm_resp_buf.aw_ready),
    .data_o   (ext_tcdm_req_buf.aw)
  );

  axi_to_mem #(
    .axi_req_t  ( axi_req_t           ),
    .axi_resp_t ( axi_resp_t          ),
    .AddrWidth  ( 32                  ),
    .DataWidth  ( AXI_DATA_C2S_WIDTH  ),
    .IdWidth    ( AXI_ID_OUT_WIDTH    ),
    .NumBanks   ( NB_EXT2MEM             )
  ) i_axi_to_mem (
    .clk_i        ( clk_cluster           ),
    .rst_ni       ( rst_ni                ),
    .busy_o       ( s_axi_to_mem_busy     ),
    .axi_req_i    ( ext_tcdm_req_buf      ),
    .axi_resp_o   ( ext_tcdm_resp_buf     ),
    .mem_req_o    ( s_ext_xbar_bus_req    ),
    .mem_gnt_i    ( s_ext_xbar_bus_gnt    ),
    .mem_addr_o   ( s_ext_xbar_bus_addr   ),
    .mem_wdata_o  ( s_ext_xbar_bus_wdata  ),
    .mem_strb_o   ( s_ext_xbar_bus_be     ),
    .mem_atop_o   ( s_ext_xbar_bus_atop   ),
    .mem_we_o     ( s_ext_xbar_bus_wen    ),
    .mem_rvalid_i ( s_ext_xbar_bus_rvalid ),
    .mem_rdata_i  ( s_ext_xbar_bus_rdata  )
  );
  for (genvar i = 0; i < NB_EXT2MEM; i++) begin : gen_ext_xbar_bus
    assign s_ext_xbar_bus[i].req     = s_ext_xbar_bus_req[i];
    assign s_ext_xbar_bus_gnt[i]     = s_ext_xbar_bus[i].gnt;
    assign s_ext_xbar_bus[i].add     = s_ext_xbar_bus_addr[i];
    assign s_ext_xbar_bus[i].wdata   = s_ext_xbar_bus_wdata[i];
    assign s_ext_xbar_bus[i].be      = s_ext_xbar_bus_be[i];
    assign s_ext_xbar_bus[i].wen     = ~s_ext_xbar_bus_wen[i]; // active low
    assign s_ext_xbar_bus_rvalid[i]  = s_ext_xbar_bus[i].r_valid;
    assign s_ext_xbar_bus_rdata[i]   = s_ext_xbar_bus[i].r_rdata;
  end

  axi2per_wrap #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH     ),
    .AXI_DATA_WIDTH ( AXI_DATA_C2S_WIDTH ),
    .AXI_ID_WIDTH   ( AXI_ID_OUT_WIDTH   ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH     )
  ) axi2per_wrap_i (
    .clk_i         ( clk_cluster       ),
    .rst_ni        ( rst_ni            ),
    .test_en_i     ( test_mode_i       ),
    .cluster_id_i  ( cluster_id_i      ),
    .axi_slave     ( s_ext_mperiph_bus ),
    .periph_master ( s_mperiph_bus     ),
    .busy_o        ( s_axi2per_busy    )
  );

  per_demux_wrap #(
    .NB_MASTERS  (  2 ),
    .ADDR_OFFSET ( 20 )
  ) per_demux_wrap_i (
    .clk_i   ( clk_cluster         ),
    .rst_ni  ( rst_ni              ),
    .slave   ( s_mperiph_bus       ),
    .masters ( s_mperiph_demux_bus )
  );

  assign s_mperiph_xbar_bus[NB_MPERIPHS-1].req   = s_mperiph_demux_bus[0].req;
  assign s_mperiph_xbar_bus[NB_MPERIPHS-1].add   = s_mperiph_demux_bus[0].add;
  assign s_mperiph_xbar_bus[NB_MPERIPHS-1].wen   = s_mperiph_demux_bus[0].wen;
  assign s_mperiph_xbar_bus[NB_MPERIPHS-1].wdata = s_mperiph_demux_bus[0].wdata;
  assign s_mperiph_xbar_bus[NB_MPERIPHS-1].be    = s_mperiph_demux_bus[0].be;

  assign s_mperiph_demux_bus[0].gnt       = s_mperiph_xbar_bus[NB_MPERIPHS-1].gnt;
  assign s_mperiph_demux_bus[0].r_valid   = s_mperiph_xbar_bus[NB_MPERIPHS-1].r_valid;
  assign s_mperiph_demux_bus[0].r_opc     = s_mperiph_xbar_bus[NB_MPERIPHS-1].r_opc;
  assign s_mperiph_demux_bus[0].r_rdata   = s_mperiph_xbar_bus[NB_MPERIPHS-1].r_rdata;

  per_demux_wrap #(
    .NB_MASTERS  ( NB_CORES ),
    .ADDR_OFFSET ( 15       )
  ) debug_interconect_i (
    .clk_i   ( clk_cluster            ),
    .rst_ni  ( rst_ni                 ),
    .slave   ( s_mperiph_demux_bus[1] ),
    .masters ( s_debug_bus            )
  );

  per2axi_wrap #(
    .NB_CORES       ( NB_CORES             ),
    .PER_ADDR_WIDTH ( 32                   ),
    .PER_ID_WIDTH   ( NB_CORES+NB_MPERIPHS ),
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH       ),
    .AXI_DATA_WIDTH ( AXI_DATA_C2S_WIDTH   ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH       ),
    .AXI_ID_WIDTH   ( AXI_ID_IN_WIDTH      )
  ) per2axi_wrap_i (
    .clk_i                ( clk_cluster                       ),
    .rst_ni               ( rst_ni                            ),
    .test_en_i            ( test_mode_i                       ),
    .periph_slave         ( s_xbar_speriph_bus[SPER_EXT_ID]   ),
    .periph_slave_atop_i  ( s_xbar_speriph_atop[SPER_EXT_ID]  ),
    .axi_axuser_i         ( tryx_axuser                       ),
    .axi_xresp_decerr_o   ( tryx_xresp_decerr                 ),
    .axi_xresp_slverr_o   ( tryx_xresp_slverr                 ),
    .axi_xresp_valid_o    ( tryx_xresp_valid                  ),
    .axi_master           ( s_core_ext_bus                    ),
    .busy_o               ( s_per2axi_busy                    )
  );

  tryx_ctrl #(
    .NB_CORES           ( NB_CORES       ),
    .AXI_USER_WIDTH     ( AXI_USER_WIDTH )
  ) tryx_ctrl_i (
    .clk_i              ( clk_cluster        ),
    .rst_ni             ( rst_ni             ),
    .axi_axuser_o       ( tryx_axuser        ),
    .axi_xresp_decerr_i ( tryx_xresp_decerr  ),
    .axi_xresp_slverr_i ( tryx_xresp_slverr  ),
    .axi_xresp_valid_i  ( tryx_xresp_valid   ),
    .periph_data_slave  ( s_core_periph_bus  ),
    .periph_data_master ( s_core_periph_tryx )
  );

  /* cluster (log + periph) interconnect and attached peripherals */
  cluster_interconnect_wrap #(
    .NB_CORES           ( NB_CORES           ),
    .NB_HWACC_PORTS     ( NB_HWACC_PORTS     ),
    .NB_DMAS            ( NB_DMAS            ),
    .NB_EXT             ( NB_EXT2MEM         ),
    .NB_MPERIPHS        ( NB_MPERIPHS        ),
    .NB_TCDM_BANKS      ( NB_TCDM_BANKS      ),
    .NB_SPERIPHS        ( NB_SPERIPHS        ),
    .DATA_WIDTH         ( DATA_WIDTH         ),
    .ADDR_WIDTH         ( ADDR_WIDTH         ),
    .BE_WIDTH           ( BE_WIDTH           ),
    .TEST_SET_BIT       ( TEST_SET_BIT       ),
    .ADDR_MEM_WIDTH     ( ADDR_MEM_WIDTH     ),
    .LOG_CLUSTER        ( LOG_CLUSTER        ),
    .PE_ROUTING_LSB     ( PE_ROUTING_LSB     ),
    .PE_ROUTING_MSB     ( PE_ROUTING_MSB     ),
    .CLUSTER_ALIAS      ( CLUSTER_ALIAS      ),
    .CLUSTER_ALIAS_BASE ( CLUSTER_ALIAS_BASE )
  ) cluster_interconnect_wrap_i (
    .clk_i                  ( clk_cluster                         ),
    .rst_ni                 ( rst_ni                              ),
    .core_tcdm_slave        ( s_core_xbar_bus                     ),
    .core_tcdm_slave_atop   ( s_core_xbar_bus_atop                ),
    .core_periph_slave      ( s_core_periph_tryx                  ),
    .core_periph_slave_atop ( s_core_periph_bus_atop              ),
    .ext_slave              ( s_ext_xbar_bus                      ),
    .ext_slave_atop         ( s_ext_xbar_bus_atop                 ),
    .dma_slave              ( s_dma_xbar_bus                      ),
    .mperiph_slave          ( s_mperiph_xbar_bus[NB_MPERIPHS-1:0] ),
    .tcdm_sram_master       ( s_tcdm_bus_sram                     ),
    .speriph_master         ( s_xbar_speriph_bus                  ),
    .speriph_master_atop    ( s_xbar_speriph_atop                 ),
    .TCDM_arb_policy_i      ( s_TCDM_arb_policy                   ),
    .s_wide_dma_a_superbanks( s_wide_dma_a_superbanks             ),
    .s_wide_dma_b_superbanks( s_wide_dma_b_superbanks             )
  );

  logic [NB_CORES-1:0] s_no_req_pending;

  dmac_wrap #(
    .NB_CORES           ( NB_CORES                                 ),
    .NB_OUTSND_BURSTS   ( NB_OUTSND_BURSTS                         ),
    .MCHAN_BURST_LENGTH ( MCHAN_BURST_LENGTH                       ),
    .AXI_ADDR_WIDTH     ( AXI_ADDR_WIDTH                           ),
    .AXI_DATA_WIDTH     ( AXI_DATA_C2S_WIDTH                       ),
    .AXI_ID_WIDTH       ( AXI_ID_IN_WIDTH                          ),
    .AXI_USER_WIDTH     ( AXI_USER_WIDTH                           ),
    .PE_ID_WIDTH        ( NB_CORES + 1                             ),
    .TCDM_ADD_WIDTH     ( TCDM_ADD_WIDTH                           ),
    .DATA_WIDTH         ( DATA_WIDTH                               ),
    .ADDR_WIDTH         ( ADDR_WIDTH                               ),
    .BE_WIDTH           ( BE_WIDTH                                 ),
    .dma_transf_descr_t ( pspin_cfg_pkg::transf_descr_32_t         ),
    .DMA_AXI_AW_WIDTH   ( DMA_AXI_AW_WIDTH                         ),
    .DMA_AXI_DW_WIDTH   ( DMA_AXI_DW_WIDTH                         ),
    .DMA_AXI_ID_WIDTH   ( DMA_AXI_ID_WIDTH                         ),
    .DMA_AXI_UW_WIDTH   ( DMA_AXI_UW_WIDTH                         ),
    .TF_REQ_FIFO_DEPTH  ( pspin_cfg_pkg::BUFFERED_HERS_PER_CLUSTER )
  ) dmac_wrap_i (
    .clk_i                 ( clk_cluster             ),
    .rst_ni                ( rst_ni                  ),
    .cluster_id_i          ( cluster_id_i            ),
    .test_mode_i           ( test_mode_i             ),
    .ctrl_slave            ( s_core_dmactrl_bus      ),
    .pe_ctrl_slave         ( s_periph_dma_bus        ),
    .tcdm_master           ( s_dma_xbar_bus          ),
    .ext_master            ( s_dma_ext_bus           ),
    .s_wide_dma_soc        ( s_wide_dma_soc          ),
    .s_wide_dma_superbanks ( s_wide_dma_a_superbanks ),
    .term_event_o          ( s_dma_event             ),
    .term_irq_o            ( s_dma_irq               ),
    .term_event_pe_o       ( s_dma_pe_event          ),
    .term_irq_pe_o         ( s_dma_pe_irq            ),
    .busy_o                ( s_dmac_busy             ),
    .ext_dma_req_valid_i   ( ext_dma_req_valid       ),
    .ext_dma_req_ready_o   ( ext_dma_req_ready       ),
    .ext_dma_req_i         ( ext_dma_req             ),
    .ext_dma_rsp_valid_o   ( ext_dma_rsp_valid       ),
    .no_req_pending_o      ( s_no_req_pending        )
  );

  nhi_port_wrap #(
    .DMA_AXI_AW_WIDTH   ( DMA_AXI_AW_WIDTH        ),
    .DMA_AXI_DW_WIDTH   ( DMA_AXI_DW_WIDTH        ),
    .DMA_AXI_ID_WIDTH   ( DMA_AXI_ID_WIDTH        ),
    .DMA_AXI_UW_WIDTH   ( DMA_AXI_UW_WIDTH        )
  ) nhi_port_wrap_i (
    .clk_i                 ( clk_cluster             ),
    .rst_ni                ( rst_ni                  ),
    .s_wide_dma_superbanks ( s_wide_dma_b_superbanks ),
    .s_wide_dma_nhi        ( s_wide_nhi_superbanks   )
  );

  cluster_peripherals #(
    .NB_CORES       ( NB_CORES       ),
    .NB_MPERIPHS    ( NB_MPERIPHS    ),
    .NB_CACHE_BANKS ( NB_CACHE_BANKS ),
    .NB_SPERIPHS    ( NB_SPERIPHS    ),
    .NB_TCDM_BANKS  ( NB_TCDM_BANKS  ),
    .NB_HWPE_PORTS  ( 1              ),
    .ROM_BOOT_ADDR  ( ROM_BOOT_ADDR  ),
    .BOOT_ADDR      ( BOOT_ADDR      ),
    .EVNT_WIDTH     ( EVNT_WIDTH     )
  ) cluster_peripherals_i (
    .clk_i                  ( clk_cluster                        ),
    .rst_ni                 ( rst_ni                             ),
    .ref_clk_i              ( ref_clk_i                          ),
    .test_mode_i            ( test_mode_i                        ),
    .busy_o                 ( s_cluster_periphs_busy             ),
    .dma_events_i           ( s_dma_event                        ),
    .dma_irq_i              ( s_dma_irq                          ),
    .en_sa_boot_i           ( en_sa_boot_i                       ),
    .fetch_en_i             ( fetch_en_i                         ),
    .boot_addr_o            ( boot_addr                          ),
    .core_busy_i            ( core_busy                          ),
    .core_clk_en_o          ( clk_core_en                        ),
    .fregfile_disable_o     ( s_fregfile_disable                 ),
    .speriph_slave          ( s_xbar_speriph_bus[NB_SPERIPHS-2:0]),
    .core_eu_direct_link    ( s_core_euctrl_bus                  ),
    .dma_cfg_master         ( s_periph_dma_bus                   ),
    .dma_pe_irq_i           ( s_dma_pe_irq                       ),
    .pf_event_o             ( s_pf_event                         ),
    .soc_periph_evt_ready_o ( s_events_ready                     ),
    .soc_periph_evt_valid_i ( s_events_valid                     ),
    .soc_periph_evt_data_i  ( s_events_data                      ),
    .dbg_core_halt_o        ( dbg_core_halt                      ),
    .dbg_core_halted_i      ( dbg_core_halted                    ),
    .dbg_core_resume_o      ( dbg_core_resume                    ),
    .eoc_o                  ( eoc_o                              ),
    .cluster_cg_en_o        ( s_cluster_cg_en                    ),
    .fetch_enable_reg_o     ( fetch_enable_reg_int               ),
    .irq_id_o               ( irq_id                             ),
    .irq_ack_id_i           ( irq_ack_id                         ),
    .irq_req_o              ( irq_req                            ),
    .irq_ack_i              ( irq_ack                            ),
    .TCDM_arb_policy_o      ( s_TCDM_arb_policy                  ),
    .hwce_cfg_master        ( s_xne_cfg_bus                      ),
    .hwacc_events_i         ( s_hwacc_events                     ),
    .hwpe_sel_o             ( hwpe_sel                           ),
    .hwpe_en_o              ( hwpe_en                            ),
    .IC_ctrl_unit_bus       (  IC_ctrl_unit_bus                  )
  );


  /* Cluster scheduler */
  cluster_scheduler #(
        .NUM_HERS_PER_CLUSTER  (pspin_cfg_pkg::NUM_HERS_PER_CLUSTER),
        .L1_PKT_BUFF_SIZE      (pspin_cfg_pkg::L1_PKT_BUFF_SIZE),
        .L1_CLUSTER_BASE       (pspin_cfg_pkg::L1_CLUSTER_BASE),
        .L1_CLUSTER_MEM_SIZE   (pspin_cfg_pkg::L1_CLUSTER_MEM_SIZE),
        .L1_RUNTIME_OFFSET     (pspin_cfg_pkg::L1_RUNTIME_OFFSET)
  ) i_cluster_scheduler (
        .rst_ni                (rst_ni),
        .clk_i                 (clk_cluster),

        .cluster_id_i          (cluster_id_i),

        // from scheduler
        .task_valid_i          (task_valid_i),
        .task_ready_o          (task_ready_o),
        .task_descr_i          (task_descr_i),

        // to scheduler
        .feedback_valid_o      (feedback_valid_o),
        .feedback_ready_i      (feedback_ready_i),
        .feedback_o            (feedback_o),

        // to DMA
        .dma_xfer_valid_o      (ext_dma_req_valid),
        .dma_xfer_ready_i      (ext_dma_req_ready),
        .dma_xfer_o            (ext_dma_req),

        // from DMA
        .dma_resp_i            (ext_dma_rsp_valid),

        // to HPU drivers
        .hpu_task_valid_o      (hpu_task_valid),
        .hpu_task_ready_i      (hpu_task_ready),
        .hpu_task_o            (hpu_task),

        // from HPU drivers
        .hpu_feedback_valid_i  (hpu_feedback_valid),
        .hpu_feedback_ready_o  (hpu_feedback_ready),
        .hpu_feedback_i        (hpu_feedback),

        .hpu_active_i          (hpu_active),
        .cluster_active_o      (cluster_active_o)
      );


    /* cluster-local command unit */
    cluster_cmd #(
      .NUM_CORES    (NB_CORES)
    ) i_cluster_cmd (
      .clk_i        (clk_cluster),
      .rst_ni       (rst_ni),

      .cmd_ready_o  (core_cmd_ready),
      .cmd_valid_i  (core_cmd_valid),
      .cmd_i        (core_cmd),

      .cmd_ready_i  (cmd_ready_i),
      .cmd_valid_o  (cmd_valid_o),
      .cmd_o        (cmd_o)
    );

  /* cluster cores + core-coupled accelerators / shared execution units */
  localparam int N_PMP_ENTRIES = 16;
  generate
    for (genvar i=0; i<NB_CORES; i++) begin : CORE

      localparam int unsigned next_i = (i == NB_CORES - 1) ? 0 : i + 1;

      logic pmp_conf_override;
      logic [N_PMP_ENTRIES-1:0] [31:0] pmp_addr;
      logic [N_PMP_ENTRIES-1:0] [7:0]  pmp_cfg;

      core_region #(
        .CORE_ID                   ( i                      ),
        .ADDR_WIDTH                ( 32                     ),
        .DATA_WIDTH                ( 32                     ),
        .INSTR_RDATA_WIDTH         ( INSTR_RDATA_WIDTH      ),
        .CLUSTER_ALIAS             ( CLUSTER_ALIAS          ),
        .CLUSTER_ALIAS_BASE        ( CLUSTER_ALIAS_BASE     ),
        .REMAP_ADDRESS             ( REMAP_ADDRESS          ),
        .DEM_PER_BEFORE_TCDM_TS    ( DEM_PER_BEFORE_TCDM_TS ),
        .INTER_CORE_FIFO_DEPTH     ( 32                     ),
        .N_PMP_ENTRIES             ( N_PMP_ENTRIES          )
      ) core_region_i (
        .clk_i                    ( clk_cluster               ),
        .rst_ni                   ( s_rst_n                   ),
        .base_addr_i              ( base_addr_i               ),
        .init_ni                  ( s_init_n                  ),
        .cluster_id_i             ( cluster_id_i              ),
        .clock_en_i               ( clk_core_en[i]            ),
        .fetch_en_i               ( fetch_en_int[i]           ),
        .fregfile_disable_i       ( s_fregfile_disable        ),
        .boot_addr_i              ( boot_addr[i]              ),
        .irq_id_i                 ( irq_id[i]                 ),
        .irq_ack_id_o             ( irq_ack_id[i]             ),
        .irq_req_i                ( irq_req[i]                ),
        .irq_ack_o                ( irq_ack[i]                ),

        .test_mode_i              ( test_mode_i               ),
        .core_busy_o              ( core_busy[i]              ),
        .instr_req_o              ( instr_req[i]              ),
        .instr_gnt_i              ( instr_gnt[i]              ),
        .instr_addr_o             ( instr_addr[i]             ),
        .instr_r_rdata_i          ( instr_r_rdata[i]          ),
        .instr_r_valid_i          ( instr_r_valid[i]          ),
        .debug_bus                ( s_debug_bus[i]            ),
        .debug_core_halted_o      ( dbg_core_halted[i]        ),
        .debug_core_halt_i        ( dbg_core_halt[i]          ),
        .debug_core_resume_i      ( dbg_core_resume[i]        ),
        .unaligned_o              ( /* unused */              ),
        .tcdm_data_master         ( s_core_xbar_bus[i]        ),
        .tcdm_data_master_atop    ( s_core_xbar_bus_atop[i]   ),
        .dma_ctrl_master          ( s_core_dmactrl_bus[i]     ),
        .eu_ctrl_master           ( s_core_euctrl_bus[i]      ),
        .periph_data_master       ( s_core_periph_bus[i]      ),
        .periph_data_master_atop  ( s_core_periph_bus_atop[i] ),
        .this_fifo_slave          ( s_inter_core_fifo[i]      ),
        .next_fifo_master         ( s_inter_core_fifo[next_i] ),
        .hpu_driver_master        ( s_hpu_driver_bus[i]       ),
        .apu_master               ( apu_cluster_bus[i]        ),

        .pmp_conf_override_i      ( pmp_conf_override         ),
        .pmp_cfg_i                ( pmp_cfg                   ),
        .pmp_addr_i               ( pmp_addr                  )
      );

      /* HPU drivers */
      //TODO: move this into core_region?
      hpu_driver #(
        .C_CORE_ID                (i),
        .L1_PKT_BUFF_SIZE         (pspin_cfg_pkg::L1_PKT_BUFF_SIZE),
        .NUM_CLUSTERS             (pspin_cfg_pkg::NUM_CLUSTERS),
        .NUM_SCRATCHPADS          (pspin_cfg_pkg::NUM_MSG_PER_CLUSTER),
        .NUM_HERS_PER_CLUSTER     (pspin_cfg_pkg::NUM_HERS_PER_CLUSTER),
        .L1_CLUSTER_BASE          (pspin_cfg_pkg::L1_CLUSTER_BASE),
        .L1_CLUSTER_MEM_SIZE      (pspin_cfg_pkg::L1_CLUSTER_MEM_SIZE),
        .L1_RUNTIME_OFFSET        (pspin_cfg_pkg::L1_RUNTIME_OFFSET),
        .L1_SCRATCHPAD_SIZE       (pspin_cfg_pkg::L1_SCRATCHPAD_SIZE),
        .NUM_CMDS                 (pspin_cfg_pkg::NUM_HPU_CMDS),
        .N_PMP_ENTRIES            (N_PMP_ENTRIES)
      ) i_hpu_driver (
          .rst_ni                 (rst_ni),
          .clk_i                  (clk_cluster),

          .cluster_id_i           (cluster_id_i),

          .hpu_task_valid_i       (hpu_task_valid[i]),
          .hpu_task_ready_o       (hpu_task_ready[i]),
          .hpu_task_i             (hpu_task),

          .hpu_feedback_valid_o   (hpu_feedback_valid[i]),
          .hpu_feedback_ready_i   (hpu_feedback_ready[i]),
          .hpu_feedback_o         (hpu_feedback[i]),

          .hpu_driver_slave_i     (s_hpu_driver_bus[i]),

          .hpu_active_o           (hpu_active[i]),

          .no_dma_req_pending_i   (s_no_req_pending[i]),

          .cmd_ready_i            (core_cmd_ready[i]),
          .cmd_valid_o            (core_cmd_valid[i]),
          .cmd_o                  (core_cmd[i]),

          .cmd_resp_valid_i       (cmd_resp_valid_i),
          .cmd_resp_i             (cmd_resp_i),

          .pmp_conf_override_o    (pmp_conf_override),
          .pmp_cfg_o              (pmp_cfg),
          .pmp_addr_o             (pmp_addr)
      );

      assign s_core_periph_bus[i].id = 1 << i;
    end
  endgenerate

  generate
    if(APU_CLUSTER) begin : apu_cluster_gen
      apu_cluster #(
        .C_NB_CORES         ( NB_CORES          ),
        .NDSFLAGS_CPU       ( NDSFLAGS_CPU      ),
        .NUSFLAGS_CPU       ( NUSFLAGS_CPU      ),
        .WOP_CPU            ( WOP_CPU           ),
        .NARGS_CPU          ( NARGS_CPU         ),
        .WAPUTYPE           ( WAPUTYPE          ),
        .SHARED_FP          ( SHARED_FP         ),
        .SHARED_DSP_MULT    ( SHARED_DSP_MULT   ),
        .SHARED_INT_MULT    ( SHARED_INT_MULT   ),
        .SHARED_INT_DIV     ( SHARED_INT_DIV    ),
        .SHARED_FP_DIVSQRT  ( SHARED_FP_DIVSQRT )
      ) apu_cluster_i (
        .clk_i  ( clk_cluster     ),
        .rst_ni ( s_rst_n         ),
        .cpus   ( apu_cluster_bus )
      );
    end
    else begin : no_apu_cluster_gen
      for(genvar i=0; i<NB_CORES; i++) begin
        assign apu_cluster_bus[i].ack_ds_s    = '1;
        assign apu_cluster_bus[i].valid_us_s  = '0;
        assign apu_cluster_bus[i].result_us_d = '0;
        assign apu_cluster_bus[i].flags_us_d  = '0;
      end
    end
  endgenerate

  /* cluster-coupled accelerators / HW processing engines */
  generate
    if(XNE_PRESENT == 1) begin : xne_gen
      xne_wrap #(
        .N_CORES       ( NB_CORES             ),
        .N_MASTER_PORT ( 4                    ),
        .ID_WIDTH      ( NB_CORES+NB_MPERIPHS )
      ) xne_wrap_i (
        .clk               ( clk_cluster                                         ),
        .rst_n             ( s_rst_n                                             ),
        .test_mode         ( test_mode_i                                         ),
        .hwacc_xbar_master ( s_core_xbar_bus[NB_CORES+NB_HWACC_PORTS-1:NB_CORES] ),
        .hwacc_cfg_slave   ( s_xne_cfg_bus                                       ),
        .evt_o             ( s_xne_evt                                           ),
        .busy_o            ( s_xne_busy                                          )
      );
    end
    else begin : no_xne_gen
      assign s_xne_cfg_bus.r_valid = '1;
      assign s_xne_cfg_bus.gnt = '1;
      assign s_xne_cfg_bus.r_rdata = 32'hdeadbeef;
      assign s_xne_cfg_bus.r_id = '0;
      for (genvar i=NB_CORES; i<NB_CORES+NB_HWACC_PORTS; i++) begin : no_xne_bias
        assign s_core_xbar_bus[i].req = '0;
        assign s_core_xbar_bus[i].wen = '0;
        assign s_core_xbar_bus[i].be  = '0;
        assign s_core_xbar_bus[i].wdata = '0;
      end
      assign s_xne_busy = '0;
      assign s_xne_evt  = '0;

    end
  endgenerate

  generate
    for(genvar i=0; i<NB_CORES; i++) begin : hwacc_event_interrupt_gen
      assign s_hwacc_events[i][3:2] = '0;
      assign s_hwacc_events[i][1:0] = s_xne_evt[i];
    end
  endgenerate

  /* instruction cache */
  icache_top_mp_128_PF #(
    .FETCH_ADDR_WIDTH ( 32                 ),
    .FETCH_DATA_WIDTH ( 128                ),
    .NB_CORES         ( NB_CORES           ),
    .NB_BANKS         ( NB_CACHE_BANKS     ),
    .NB_WAYS          ( SET_ASSOCIATIVE    ),
    .CACHE_SIZE       ( CACHE_SIZE         ),
    .CACHE_LINE       ( 1                  ),
    .AXI_ID           ( AXI_ID_OUT_WIDTH   ),
    .AXI_ADDR         ( AXI_ADDR_WIDTH     ),
    .AXI_USER         ( AXI_USER_WIDTH     ),
    .AXI_DATA         ( AXI_DATA_C2S_WIDTH ),
    .USE_REDUCED_TAG  ( USE_REDUCED_TAG    ),
    .L2_SIZE          ( L2_SIZE            )
  ) icache_top_i (
    .clk                    ( clk_cluster         ),
    .rst_n                  ( s_rst_n             ),
    .test_en_i              ( test_mode_i         ),
    .fetch_req_i            ( instr_req           ),
    .fetch_addr_i           ( instr_addr          ),
    .fetch_gnt_o            ( instr_gnt           ),
    .fetch_rvalid_o         ( instr_r_valid       ),
    .fetch_rdata_o          ( instr_r_rdata       ),
    .axi_master_arid_o      ( icache_ar_id_o      ),
    .axi_master_araddr_o    ( icache_ar_addr_o    ),
    .axi_master_arlen_o     ( icache_ar_len_o     ),
    .axi_master_arsize_o    ( icache_ar_size_o    ),
    .axi_master_arburst_o   ( icache_ar_burst_o   ),
    .axi_master_arlock_o    ( icache_ar_lock_o    ),
    .axi_master_arcache_o   ( icache_ar_cache_o   ),
    .axi_master_arprot_o    ( icache_ar_prot_o    ),
    .axi_master_arregion_o  ( icache_ar_region_o  ),
    .axi_master_aruser_o    ( icache_ar_user_o    ),
    .axi_master_arqos_o     ( icache_ar_qos_o     ),
    .axi_master_arvalid_o   ( icache_ar_valid_o   ),
    .axi_master_arready_i   ( icache_ar_ready_i   ),
    .axi_master_rid_i       ( icache_r_id_i       ),
    .axi_master_rdata_i     ( icache_r_data_i     ),
    .axi_master_rresp_i     ( icache_r_resp_i     ),
    .axi_master_rlast_i     ( icache_r_last_i     ),
    .axi_master_ruser_i     ( icache_r_user_i     ),
    .axi_master_rvalid_i    ( icache_r_valid_i    ),
    .axi_master_rready_o    ( icache_r_ready_o    ),
    .axi_master_awid_o      ( icache_aw_id_o      ),
    .axi_master_awaddr_o    ( icache_aw_addr_o    ),
    .axi_master_awlen_o     ( icache_aw_len_o     ),
    .axi_master_awsize_o    ( icache_aw_size_o    ),
    .axi_master_awburst_o   ( icache_aw_burst_o   ),
    .axi_master_awlock_o    ( icache_aw_lock_o    ),
    .axi_master_awcache_o   ( icache_aw_cache_o   ),
    .axi_master_awprot_o    ( icache_aw_prot_o    ),
    .axi_master_awregion_o  ( icache_aw_region_o  ),
    .axi_master_awuser_o    ( icache_aw_user_o    ),
    .axi_master_awqos_o     ( icache_aw_qos_o     ),
    .axi_master_awvalid_o   ( icache_aw_valid_o   ),
    .axi_master_awready_i   ( icache_aw_ready_i   ),
    .axi_master_wdata_o     ( icache_w_data_o     ),
    .axi_master_wstrb_o     ( icache_w_strb_o     ),
    .axi_master_wlast_o     ( icache_w_last_o     ),
    .axi_master_wuser_o     ( icache_w_user_o     ),
    .axi_master_wvalid_o    ( icache_w_valid_o    ),
    .axi_master_wready_i    ( icache_w_ready_i    ),
    .axi_master_bid_i       ( icache_b_id_i       ),
    .axi_master_bresp_i     ( icache_b_resp_i     ),
    .axi_master_buser_i     ( icache_b_user_i     ),
    .axi_master_bvalid_i    ( icache_b_valid_i    ),
    .axi_master_bready_o    ( icache_b_ready_o    ),
    .IC_ctrl_unit_slave_if  ( IC_ctrl_unit_bus    )
  );
  assign icache_aw_atop_o = '0;

  /* TCDM banks */
  for (genvar i = 0; i < NB_TCDM_BANKS; i++) begin : gen_tcdm_banks
    logic [$clog2(TCDM_NUM_ROWS)-1:0] addr;
    assign addr = s_tcdm_bus_sram[i].add;

    sram #(
      .N_WORDS    (TCDM_NUM_ROWS),
      .DATA_WIDTH (32)
    ) i_mem (
      .clk_i    (clk_cluster),
      .rst_ni   (rst_ni),
      .req_i    (s_tcdm_bus_sram[i].req),
      .addr_i   (addr),
      .we_i     (~s_tcdm_bus_sram[i].wen),
      .wdata_i  (s_tcdm_bus_sram[i].wdata),
      .be_i     (s_tcdm_bus_sram[i].be),
      .rdata_o  (s_tcdm_bus_sram[i].rdata)
    );
  end

  if (ASYNC_INTF) begin : gen_axi_slice_dc
    axi_slice_dc_slave_wrap #(
      .AXI_ADDR_WIDTH  ( AXI_ADDR_WIDTH         ),
      .AXI_DATA_WIDTH  ( AXI_DATA_C2S_WIDTH     ),
      .AXI_USER_WIDTH  ( AXI_USER_WIDTH         ),
      .AXI_ID_WIDTH    ( AXI_ID_OUT_WIDTH       ),
      .BUFFER_WIDTH    ( DC_SLICE_BUFFER_WIDTH  )
    ) data_master_slice_i (
      .clk_i            ( clk_cluster         ),
      .rst_ni           ( s_rst_n             ),
      .test_cgbypass_i  ( 1'b0                ),
      .isolate_i        ( 1'b0                ),
      .axi_slave        ( s_data_master       ),
      .axi_master_async ( s_data_master_async )
    );
    axi_slice_dc_master_wrap #(
      .AXI_ADDR_WIDTH  ( AXI_ADDR_WIDTH        ),
      .AXI_DATA_WIDTH  ( AXI_DATA_S2C_WIDTH    ),
      .AXI_USER_WIDTH  ( AXI_USER_WIDTH        ),
      .AXI_ID_WIDTH    ( AXI_ID_IN_WIDTH       ),
      .BUFFER_WIDTH    ( DC_SLICE_BUFFER_WIDTH )
    ) data_slave_slice_i (
      .clk_i           ( clk_i              ),
      .rst_ni          ( s_rst_n            ),
      .test_cgbypass_i ( 1'b0               ),
      .isolate_i       ( 1'b0               ),
      .clock_down_i    ( s_isolate_cluster  ),
      .incoming_req_o  ( s_incoming_req     ),
      .axi_slave_async ( s_data_slave_async ),
      .axi_master      ( s_data_slave       )
    );

  end else begin : gen_axi_cut
    axi_cut_intf #(
      .ADDR_WIDTH ( AXI_ADDR_WIDTH      ),
      .DATA_WIDTH ( AXI_DATA_C2S_WIDTH  ),
      .ID_WIDTH   ( AXI_ID_OUT_WIDTH    ),
      .USER_WIDTH ( AXI_USER_WIDTH      )
    ) i_data_master_cut (
      .clk_i,
      .rst_ni,
      .in     (s_data_master),
      .out    (s_data_master_cut)
    );
    axi_cut_intf #(
      .ADDR_WIDTH ( AXI_ADDR_WIDTH      ),
      .DATA_WIDTH ( AXI_DATA_S2C_WIDTH  ),
      .ID_WIDTH   ( AXI_ID_IN_WIDTH    ),
      .USER_WIDTH ( AXI_USER_WIDTH      )
    ) i_data_slave_cut (
      .clk_i,
      .rst_ni,
      .in     (s_data_slave_cut),
      .out    (s_data_slave)
    );
    // pragma translate_off
    always @(posedge clk_i or posedge clk_cluster) begin
      assert (clk_cluster == clk_i)
        else $error("Cluster clock differs from clock input but asynchronous input inactive!");
    end
    // pragma translate_on
  end

   // TODO: distinguish async / sync case
  /* event synchronizers */
  dc_token_ring_fifo_dout #(
    .DATA_WIDTH   ( EVNT_WIDTH            ),
    .BUFFER_DEPTH ( DC_SLICE_BUFFER_WIDTH )
  ) u_event_dc (
    .clk          ( clk_i                    ),
    .rstn         ( s_rst_n                  ),
    .data         ( s_events_data            ),
    .valid        ( s_events_valid           ),
    .ready        ( s_events_ready           ),
    .write_token  ( ext_events_writetoken_i  ),
    .read_pointer ( ext_events_readpointer_o ),
    .data_async   ( ext_events_dataasync_i   )
  );
  assign s_events_async = s_events_valid;

  edge_propagator_tx ep_dma_pe_evt_i (
    .clk_i   ( clk_i              ),
    .rstn_i  ( s_rst_n            ),
    .valid_i ( s_dma_pe_event     ),
    .ack_i   ( dma_pe_evt_ack_i   ),
    .valid_o ( dma_pe_evt_valid_o )
  );

  edge_propagator_tx ep_dma_pe_irq_i (
    .clk_i   ( clk_i              ),
    .rstn_i  ( s_rst_n            ),
    .valid_i ( s_dma_pe_irq       ),
    .ack_i   ( dma_pe_irq_ack_i   ),
    .valid_o ( dma_pe_irq_valid_o )
  );

  edge_propagator_tx ep_pf_evt_i (
    .clk_i   ( clk_i          ),
    .rstn_i  ( s_rst_n        ),
    .valid_i ( s_pf_event     ),
    .ack_i   ( pf_evt_ack_i   ),
    .valid_o ( pf_evt_valid_o )
  );

  if (ASYNC_INTF) begin : gen_cluster_clock_gate
    /* centralized gating */
    cluster_clock_gate #(
      .NB_CORES ( NB_CORES )
    ) u_clustercg (
      .clk_i              ( clk_i              ),
      .rstn_i             ( s_rst_n            ),
      .test_mode_i        ( test_mode_i        ),
      .cluster_cg_en_i    ( s_cluster_cg_en    ),
      .cluster_int_busy_i ( s_cluster_int_busy ),
      .cores_busy_i       ( core_busy          ),
      .events_i           ( s_events_async     ),
      .incoming_req_i     ( s_incoming_req     ),
      .isolate_cluster_o  ( s_isolate_cluster  ),
      .cluster_clk_o      ( clk_cluster        )
    );
  end else begin : gen_no_cluster_clock_gate
    assign clk_cluster = clk_i;
  end

  /* binding of AXI SV interfaces to external Verilog buses */
  if (ASYNC_INTF) begin : gen_bind_async_intf
    assign s_data_slave_async.aw_writetoken   = data_slave_aw_writetoken_i;
    assign s_data_slave_async.aw_addr         = data_slave_aw_addr_i;
    assign s_data_slave_async.aw_prot         = data_slave_aw_prot_i;
    assign s_data_slave_async.aw_region       = data_slave_aw_region_i;
    assign s_data_slave_async.aw_len          = data_slave_aw_len_i;
    assign s_data_slave_async.aw_size         = data_slave_aw_size_i;
    assign s_data_slave_async.aw_burst        = data_slave_aw_burst_i;
    assign s_data_slave_async.aw_lock         = data_slave_aw_lock_i;
    assign s_data_slave_async.aw_atop         = data_slave_aw_atop_i;
    assign s_data_slave_async.aw_cache        = data_slave_aw_cache_i;
    assign s_data_slave_async.aw_qos          = data_slave_aw_qos_i;
    assign s_data_slave_async.aw_id           = data_slave_aw_id_i;
    assign s_data_slave_async.aw_user         = data_slave_aw_user_i;
    assign data_slave_aw_readpointer_o        = s_data_slave_async.aw_readpointer;

    assign s_data_slave_async.ar_writetoken   = data_slave_ar_writetoken_i;
    assign s_data_slave_async.ar_addr         = data_slave_ar_addr_i;
    assign s_data_slave_async.ar_prot         = data_slave_ar_prot_i;
    assign s_data_slave_async.ar_region       = data_slave_ar_region_i;
    assign s_data_slave_async.ar_len          = data_slave_ar_len_i;
    assign s_data_slave_async.ar_size         = data_slave_ar_size_i;
    assign s_data_slave_async.ar_burst        = data_slave_ar_burst_i;
    assign s_data_slave_async.ar_lock         = data_slave_ar_lock_i;
    assign s_data_slave_async.ar_cache        = data_slave_ar_cache_i;
    assign s_data_slave_async.ar_qos          = data_slave_ar_qos_i;
    assign s_data_slave_async.ar_id           = data_slave_ar_id_i;
    assign s_data_slave_async.ar_user         = data_slave_ar_user_i;
    assign data_slave_ar_readpointer_o        = s_data_slave_async.ar_readpointer;

    assign s_data_slave_async.w_writetoken    = data_slave_w_writetoken_i;
    assign s_data_slave_async.w_data          = data_slave_w_data_i;
    assign s_data_slave_async.w_strb          = data_slave_w_strb_i;
    assign s_data_slave_async.w_user          = data_slave_w_user_i;
    assign s_data_slave_async.w_last          = data_slave_w_last_i;
    assign data_slave_w_readpointer_o         = s_data_slave_async.w_readpointer;

    assign data_slave_r_writetoken_o          = s_data_slave_async.r_writetoken;
    assign data_slave_r_data_o                = s_data_slave_async.r_data;
    assign data_slave_r_resp_o                = s_data_slave_async.r_resp;
    assign data_slave_r_last_o                = s_data_slave_async.r_last;
    assign data_slave_r_id_o                  = s_data_slave_async.r_id;
    assign data_slave_r_user_o                = s_data_slave_async.r_user;
    assign s_data_slave_async.r_readpointer   = data_slave_r_readpointer_i;

    assign data_slave_b_writetoken_o          = s_data_slave_async.b_writetoken;
    assign data_slave_b_resp_o                = s_data_slave_async.b_resp;
    assign data_slave_b_id_o                  = s_data_slave_async.b_id;
    assign data_slave_b_user_o                = s_data_slave_async.b_user;
    assign s_data_slave_async.b_readpointer   = data_slave_b_readpointer_i;

    assign data_master_aw_writetoken_o        = s_data_master_async.aw_writetoken;
    assign data_master_aw_addr_o              = s_data_master_async.aw_addr;
    assign data_master_aw_prot_o              = s_data_master_async.aw_prot;
    assign data_master_aw_region_o            = s_data_master_async.aw_region;
    assign data_master_aw_len_o               = s_data_master_async.aw_len;
    assign data_master_aw_size_o              = s_data_master_async.aw_size;
    assign data_master_aw_burst_o             = s_data_master_async.aw_burst;
    assign data_master_aw_lock_o              = s_data_master_async.aw_lock;
    assign data_master_aw_atop_o              = s_data_master_async.aw_atop;
    assign data_master_aw_cache_o             = s_data_master_async.aw_cache;
    assign data_master_aw_qos_o               = s_data_master_async.aw_qos;
    assign data_master_aw_id_o                = s_data_master_async.aw_id;
    assign data_master_aw_user_o              = s_data_master_async.aw_user;
    assign s_data_master_async.aw_readpointer = data_master_aw_readpointer_i;

    assign data_master_ar_writetoken_o        = s_data_master_async.ar_writetoken;
    assign data_master_ar_addr_o              = s_data_master_async.ar_addr;
    assign data_master_ar_prot_o              = s_data_master_async.ar_prot;
    assign data_master_ar_region_o            = s_data_master_async.ar_region;
    assign data_master_ar_len_o               = s_data_master_async.ar_len;
    assign data_master_ar_size_o              = s_data_master_async.ar_size;
    assign data_master_ar_burst_o             = s_data_master_async.ar_burst;
    assign data_master_ar_lock_o              = s_data_master_async.ar_lock;
    assign data_master_ar_cache_o             = s_data_master_async.ar_cache;
    assign data_master_ar_qos_o               = s_data_master_async.ar_qos;
    assign data_master_ar_id_o                = s_data_master_async.ar_id;
    assign data_master_ar_user_o              = s_data_master_async.ar_user;
    assign s_data_master_async.ar_readpointer = data_master_ar_readpointer_i;

    assign data_master_w_writetoken_o         = s_data_master_async.w_writetoken;
    assign data_master_w_data_o               = s_data_master_async.w_data;
    assign data_master_w_strb_o               = s_data_master_async.w_strb;
    assign data_master_w_user_o               = s_data_master_async.w_user;
    assign data_master_w_last_o               = s_data_master_async.w_last;
    assign s_data_master_async.w_readpointer  = data_master_w_readpointer_i;

    assign s_data_master_async.r_writetoken   = data_master_r_writetoken_i;
    assign s_data_master_async.r_data         = data_master_r_data_i;
    assign s_data_master_async.r_resp         = data_master_r_resp_i;
    assign s_data_master_async.r_last         = data_master_r_last_i;
    assign s_data_master_async.r_id           = data_master_r_id_i;
    assign s_data_master_async.r_user         = data_master_r_user_i;
    assign data_master_r_readpointer_o        = s_data_master_async.r_readpointer;

    assign s_data_master_async.b_writetoken   = data_master_b_writetoken_i;
    assign s_data_master_async.b_resp         = data_master_b_resp_i;
    assign s_data_master_async.b_id           = data_master_b_id_i;
    assign s_data_master_async.b_user         = data_master_b_user_i;
    assign data_master_b_readpointer_o        = s_data_master_async.b_readpointer;

  end else begin : gen_bind_sync_intf
    assign s_data_slave_cut.aw_addr   = data_slave_aw_addr_i;
    assign s_data_slave_cut.aw_prot   = data_slave_aw_prot_i;
    assign s_data_slave_cut.aw_region = data_slave_aw_region_i;
    assign s_data_slave_cut.aw_len    = data_slave_aw_len_i;
    assign s_data_slave_cut.aw_size   = data_slave_aw_size_i;
    assign s_data_slave_cut.aw_burst  = data_slave_aw_burst_i;
    assign s_data_slave_cut.aw_lock   = data_slave_aw_lock_i;
    assign s_data_slave_cut.aw_atop   = data_slave_aw_atop_i;
    assign s_data_slave_cut.aw_cache  = data_slave_aw_cache_i;
    assign s_data_slave_cut.aw_qos    = data_slave_aw_qos_i;
    assign s_data_slave_cut.aw_id     = data_slave_aw_id_i;
    assign s_data_slave_cut.aw_user   = data_slave_aw_user_i;
    assign s_data_slave_cut.aw_valid  = data_slave_aw_valid_i;
    assign data_slave_aw_ready_o      = s_data_slave_cut.aw_ready;

    assign s_data_slave_cut.ar_valid  = data_slave_ar_valid_i;
    assign s_data_slave_cut.ar_addr   = data_slave_ar_addr_i;
    assign s_data_slave_cut.ar_prot   = data_slave_ar_prot_i;
    assign s_data_slave_cut.ar_region = data_slave_ar_region_i;
    assign s_data_slave_cut.ar_len    = data_slave_ar_len_i;
    assign s_data_slave_cut.ar_size   = data_slave_ar_size_i;
    assign s_data_slave_cut.ar_burst  = data_slave_ar_burst_i;
    assign s_data_slave_cut.ar_lock   = data_slave_ar_lock_i;
    assign s_data_slave_cut.ar_cache  = data_slave_ar_cache_i;
    assign s_data_slave_cut.ar_qos    = data_slave_ar_qos_i;
    assign s_data_slave_cut.ar_id     = data_slave_ar_id_i;
    assign s_data_slave_cut.ar_user   = data_slave_ar_user_i;
    assign data_slave_ar_ready_o      = s_data_slave_cut.ar_ready;

    assign s_data_slave_cut.w_valid   = data_slave_w_valid_i;
    assign s_data_slave_cut.w_data    = data_slave_w_data_i;
    assign s_data_slave_cut.w_strb    = data_slave_w_strb_i;
    assign s_data_slave_cut.w_user    = data_slave_w_user_i;
    assign s_data_slave_cut.w_last    = data_slave_w_last_i;
    assign data_slave_w_ready_o       = s_data_slave_cut.w_ready;

    assign data_slave_r_valid_o       = s_data_slave_cut.r_valid;
    assign data_slave_r_data_o        = s_data_slave_cut.r_data;
    assign data_slave_r_resp_o        = s_data_slave_cut.r_resp;
    assign data_slave_r_last_o        = s_data_slave_cut.r_last;
    assign data_slave_r_id_o          = s_data_slave_cut.r_id;
    assign data_slave_r_user_o        = s_data_slave_cut.r_user;
    assign s_data_slave_cut.r_ready   = data_slave_r_ready_i;

    assign data_slave_b_valid_o       = s_data_slave_cut.b_valid;
    assign data_slave_b_resp_o        = s_data_slave_cut.b_resp;
    assign data_slave_b_id_o          = s_data_slave_cut.b_id;
    assign data_slave_b_user_o        = s_data_slave_cut.b_user;
    assign s_data_slave_cut.b_ready   = data_slave_b_ready_i;

    assign data_master_aw_valid_o     = s_data_master_cut.aw_valid;
    assign data_master_aw_addr_o      = s_data_master_cut.aw_addr;
    assign data_master_aw_prot_o      = s_data_master_cut.aw_prot;
    assign data_master_aw_region_o    = s_data_master_cut.aw_region;
    assign data_master_aw_len_o       = s_data_master_cut.aw_len;
    assign data_master_aw_size_o      = s_data_master_cut.aw_size;
    assign data_master_aw_burst_o     = s_data_master_cut.aw_burst;
    assign data_master_aw_lock_o      = s_data_master_cut.aw_lock;
    assign data_master_aw_atop_o      = s_data_master_cut.aw_atop;
    assign data_master_aw_cache_o     = s_data_master_cut.aw_cache;
    assign data_master_aw_qos_o       = s_data_master_cut.aw_qos;
    assign data_master_aw_id_o        = s_data_master_cut.aw_id;
    assign data_master_aw_user_o      = s_data_master_cut.aw_user;
    assign s_data_master_cut.aw_ready = data_master_aw_ready_i;

    assign data_master_ar_valid_o     = s_data_master_cut.ar_valid;
    assign data_master_ar_addr_o      = s_data_master_cut.ar_addr;
    assign data_master_ar_prot_o      = s_data_master_cut.ar_prot;
    assign data_master_ar_region_o    = s_data_master_cut.ar_region;
    assign data_master_ar_len_o       = s_data_master_cut.ar_len;
    assign data_master_ar_size_o      = s_data_master_cut.ar_size;
    assign data_master_ar_burst_o     = s_data_master_cut.ar_burst;
    assign data_master_ar_lock_o      = s_data_master_cut.ar_lock;
    assign data_master_ar_cache_o     = s_data_master_cut.ar_cache;
    assign data_master_ar_qos_o       = s_data_master_cut.ar_qos;
    assign data_master_ar_id_o        = s_data_master_cut.ar_id;
    assign data_master_ar_user_o      = s_data_master_cut.ar_user;
    assign s_data_master_cut.ar_ready = data_master_ar_ready_i;

    assign data_master_w_valid_o      = s_data_master_cut.w_valid;
    assign data_master_w_data_o       = s_data_master_cut.w_data;
    assign data_master_w_strb_o       = s_data_master_cut.w_strb;
    assign data_master_w_user_o       = s_data_master_cut.w_user;
    assign data_master_w_last_o       = s_data_master_cut.w_last;
    assign s_data_master_cut.w_ready  = data_master_w_ready_i;

    assign s_data_master_cut.r_valid  = data_master_r_valid_i;
    assign s_data_master_cut.r_data   = data_master_r_data_i;
    assign s_data_master_cut.r_resp   = data_master_r_resp_i;
    assign s_data_master_cut.r_last   = data_master_r_last_i;
    assign s_data_master_cut.r_id     = data_master_r_id_i;
    assign s_data_master_cut.r_user   = data_master_r_user_i;
    assign data_master_r_ready_o      = s_data_master_cut.r_ready;

    assign s_data_master_cut.b_valid  = data_master_b_valid_i;
    assign s_data_master_cut.b_resp   = data_master_b_resp_i;
    assign s_data_master_cut.b_id     = data_master_b_id_i;
    assign s_data_master_cut.b_user   = data_master_b_user_i;
    assign data_master_b_ready_o      = s_data_master_cut.b_ready;
  end

  // unpack top-level AXI for DMA MASTER
  assign dma_aw_addr_o            = s_wide_dma_soc.aw_addr;
  assign dma_aw_prot_o            = s_wide_dma_soc.aw_prot;
  assign dma_aw_region_o          = s_wide_dma_soc.aw_region;
  assign dma_aw_len_o             = s_wide_dma_soc.aw_len;
  assign dma_aw_size_o            = s_wide_dma_soc.aw_size;
  assign dma_aw_burst_o           = s_wide_dma_soc.aw_burst;
  assign dma_aw_lock_o            = s_wide_dma_soc.aw_lock;
  assign dma_aw_atop_o            = s_wide_dma_soc.aw_atop;
  assign dma_aw_cache_o           = s_wide_dma_soc.aw_cache;
  assign dma_aw_qos_o             = s_wide_dma_soc.aw_qos;
  assign dma_aw_id_o              = s_wide_dma_soc.aw_id;
  assign dma_aw_user_o            = s_wide_dma_soc.aw_user;
  assign dma_aw_valid_o           = s_wide_dma_soc.aw_valid;
  assign s_wide_dma_soc.aw_ready  = dma_aw_ready_i;
  assign dma_ar_addr_o            = s_wide_dma_soc.ar_addr;
  assign dma_ar_prot_o            = s_wide_dma_soc.ar_prot;
  assign dma_ar_region_o          = s_wide_dma_soc.ar_region;
  assign dma_ar_len_o             = s_wide_dma_soc.ar_len;
  assign dma_ar_size_o            = s_wide_dma_soc.ar_size;
  assign dma_ar_burst_o           = s_wide_dma_soc.ar_burst;
  assign dma_ar_lock_o            = s_wide_dma_soc.ar_lock;
  assign dma_ar_cache_o           = s_wide_dma_soc.ar_cache;
  assign dma_ar_qos_o             = s_wide_dma_soc.ar_qos;
  assign dma_ar_id_o              = s_wide_dma_soc.ar_id;
  assign dma_ar_user_o            = s_wide_dma_soc.ar_user;
  assign dma_ar_valid_o           = s_wide_dma_soc.ar_valid;
  assign s_wide_dma_soc.ar_ready  = dma_ar_ready_i;
  assign dma_w_data_o             = s_wide_dma_soc.w_data;
  assign dma_w_strb_o             = s_wide_dma_soc.w_strb;
  assign dma_w_user_o             = s_wide_dma_soc.w_user;
  assign dma_w_last_o             = s_wide_dma_soc.w_last;
  assign dma_w_valid_o            = s_wide_dma_soc.w_valid;
  assign s_wide_dma_soc.w_ready   = dma_w_ready_i;
  assign s_wide_dma_soc.r_data    = dma_r_data_i;
  assign s_wide_dma_soc.r_resp    = dma_r_resp_i;
  assign s_wide_dma_soc.r_last    = dma_r_last_i;
  assign s_wide_dma_soc.r_id      = dma_r_id_i;
  assign s_wide_dma_soc.r_user    = dma_r_user_i;
  assign s_wide_dma_soc.r_valid   = dma_r_valid_i;
  assign dma_r_ready_o            = s_wide_dma_soc.r_ready;
  assign s_wide_dma_soc.b_resp    = dma_b_resp_i;
  assign s_wide_dma_soc.b_id      = dma_b_id_i;
  assign s_wide_dma_soc.b_user    = dma_b_user_i;
  assign s_wide_dma_soc.b_valid   = dma_b_valid_i;
  assign dma_b_ready_o            = s_wide_dma_soc.b_ready;

  // pack top-level AXI for DMA NHI salve
  assign s_wide_nhi_superbanks.aw_addr          = nhi_aw_addr_i;
  assign s_wide_nhi_superbanks.aw_prot          = nhi_aw_prot_i;
  assign s_wide_nhi_superbanks.aw_region        = nhi_aw_region_i;
  assign s_wide_nhi_superbanks.aw_len           = nhi_aw_len_i;
  assign s_wide_nhi_superbanks.aw_size          = nhi_aw_size_i;
  assign s_wide_nhi_superbanks.aw_burst         = nhi_aw_burst_i;
  assign s_wide_nhi_superbanks.aw_lock          = nhi_aw_lock_i;
  assign s_wide_nhi_superbanks.aw_atop          = nhi_aw_atop_i;
  assign s_wide_nhi_superbanks.aw_cache         = nhi_aw_cache_i;
  assign s_wide_nhi_superbanks.aw_qos           = nhi_aw_qos_i;
  assign s_wide_nhi_superbanks.aw_id            = nhi_aw_id_i;
  assign s_wide_nhi_superbanks.aw_user          = nhi_aw_user_i;
  assign s_wide_nhi_superbanks.aw_valid         = nhi_aw_valid_i;
  assign nhi_aw_ready_o                         = s_wide_nhi_superbanks.aw_ready;
  assign s_wide_nhi_superbanks.ar_addr          = nhi_ar_addr_i;
  assign s_wide_nhi_superbanks.ar_prot          = nhi_ar_prot_i;
  assign s_wide_nhi_superbanks.ar_region        = nhi_ar_region_i;
  assign s_wide_nhi_superbanks.ar_len           = nhi_ar_len_i;
  assign s_wide_nhi_superbanks.ar_size          = nhi_ar_size_i;
  assign s_wide_nhi_superbanks.ar_burst         = nhi_ar_burst_i;
  assign s_wide_nhi_superbanks.ar_lock          = nhi_ar_lock_i;
  assign s_wide_nhi_superbanks.ar_cache         = nhi_ar_cache_i;
  assign s_wide_nhi_superbanks.ar_qos           = nhi_ar_qos_i;
  assign s_wide_nhi_superbanks.ar_id            = nhi_ar_id_i;
  assign s_wide_nhi_superbanks.ar_user          = nhi_ar_user_i;
  assign s_wide_nhi_superbanks.ar_valid         = nhi_ar_valid_i;
  assign nhi_ar_ready_o                         = s_wide_nhi_superbanks.ar_ready;
  assign s_wide_nhi_superbanks.w_data           = nhi_w_data_i;
  assign s_wide_nhi_superbanks.w_strb           = nhi_w_strb_i;
  assign s_wide_nhi_superbanks.w_user           = nhi_w_user_i;
  assign s_wide_nhi_superbanks.w_last           = nhi_w_last_i;
  assign s_wide_nhi_superbanks.w_valid          = nhi_w_valid_i;
  assign nhi_w_ready_o                          = s_wide_nhi_superbanks.w_ready;
  assign nhi_r_data_o                           = s_wide_nhi_superbanks.r_data;
  assign nhi_r_resp_o                           = s_wide_nhi_superbanks.r_resp;
  assign nhi_r_last_o                           = s_wide_nhi_superbanks.r_last;
  assign nhi_r_id_o                             = s_wide_nhi_superbanks.r_id;
  assign nhi_r_user_o                           = s_wide_nhi_superbanks.r_user;
  assign nhi_r_valid_o                          = s_wide_nhi_superbanks.r_valid;
  assign s_wide_nhi_superbanks.r_ready          = nhi_r_ready_i;
  assign nhi_b_resp_o                           = s_wide_nhi_superbanks.b_resp;
  assign nhi_b_id_o                             = s_wide_nhi_superbanks.b_id;
  assign nhi_b_user_o                           = s_wide_nhi_superbanks.b_user;
  assign nhi_b_valid_o                          = s_wide_nhi_superbanks.b_valid;
  assign s_wide_nhi_superbanks.b_ready          = nhi_b_ready_i;

endmodule
