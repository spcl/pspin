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
 * cluster_interconnect_wrap.sv
 * Davide Rossi <davide.rossi@unibo.it>
 * Antonio Pullini <pullinia@iis.ee.ethz.ch>
 * Igor Loi <igor.loi@unibo.it>
 * Francesco Conti <fconti@iis.ee.ethz.ch>
 * Thomas Benz <tbenz@iis.ee.ethz.ch>
 */

module cluster_interconnect_wrap
#(
  parameter NB_CORES        = 8,
  parameter NB_HWACC_PORTS  = 4,
  parameter NB_DMAS         = 4,
  parameter NB_EXT          = 4,
  parameter NB_MPERIPHS     = 1,
  parameter NB_TCDM_BANKS   = 16,
  parameter NB_SPERIPHS     = 3,
  parameter DATA_WIDTH      = 32,
  parameter ADDR_WIDTH      = 32,
  parameter BE_WIDTH        = DATA_WIDTH/8,
  //TCDM PARAMETERS
  parameter TEST_SET_BIT    = 20,
  parameter ADDR_MEM_WIDTH  = 11,
  parameter LOG_CLUSTER     = 5,
  parameter PE_ROUTING_LSB  = 16,
  parameter PE_ROUTING_MSB  = 19,
  parameter CLUSTER_ALIAS      = 1'b0,
  parameter CLUSTER_ALIAS_BASE = 12'h000
)
(
  input logic                          clk_i,
  input logic                          rst_ni,
  XBAR_TCDM_BUS.Slave                  core_tcdm_slave[NB_CORES+NB_HWACC_PORTS-1:0],
  input logic [NB_CORES-1:0][5:0]      core_tcdm_slave_atop,
  XBAR_PERIPH_BUS.Slave                core_periph_slave[NB_CORES-1:0],
  input logic [NB_CORES-1:0][5:0]      core_periph_slave_atop,
  XBAR_TCDM_BUS.Slave                  ext_slave[NB_EXT-1:0],
  input logic [NB_EXT-1:0][5:0]        ext_slave_atop,
  XBAR_TCDM_BUS.Slave                  dma_slave[NB_DMAS-1:0],
  XBAR_TCDM_BUS.Slave                  mperiph_slave[NB_MPERIPHS-1:0],
  TCDM_BANK_MEM_BUS.Master             tcdm_sram_master[NB_TCDM_BANKS-1:0],
  XBAR_PERIPH_BUS.Master               speriph_master[NB_SPERIPHS-1:0],
  output logic [NB_SPERIPHS-1:0][5:0]  speriph_master_atop,
  input logic [1:0]                    TCDM_arb_policy_i,
  WIDE_DMA_TCDM_BUS.Slave              s_wide_dma_a_superbanks,
  WIDE_DMA_TCDM_BUS.Slave              s_wide_dma_b_superbanks
);

  localparam TCDM_ID_WIDTH = NB_CORES+NB_DMAS+NB_EXT+NB_HWACC_PORTS;

  localparam DMA_DATA_WIDTH      = 512;
  localparam DMA_ADDR_WIDTH      = 64;
  localparam BANKS_PER_SUPERBANK = DMA_DATA_WIDTH / DATA_WIDTH;
  localparam NB_SUPERBANKS       = NB_TCDM_BANKS / BANKS_PER_SUPERBANK;

  // DMA --> LOGARITHMIC INTERCONNECT BUS SIGNALS
  logic [NB_EXT+NB_DMAS-1:0][DATA_WIDTH-1:0] s_dma_bus_wdata;
  logic [NB_EXT+NB_DMAS-1:0][ADDR_WIDTH-1:0] s_dma_bus_add;
  logic [NB_EXT+NB_DMAS-1:0]                 s_dma_bus_req;
  logic [NB_EXT+NB_DMAS-1:0]                 s_dma_bus_wen;
  logic [NB_EXT+NB_DMAS-1:0][BE_WIDTH-1:0]   s_dma_bus_be;
  logic [NB_EXT+NB_DMAS-1:0]                 s_dma_bus_gnt;
  logic [NB_EXT+NB_DMAS-1:0][DATA_WIDTH-1:0] s_dma_bus_r_rdata;
  logic [NB_EXT+NB_DMAS-1:0]                 s_dma_bus_r_valid;

  // MASTER PERIPHERALS --> PERIPHERAL INTERCONNECT BUS SIGNALS
  logic [NB_MPERIPHS-1:0][DATA_WIDTH-1:0] s_mperiph_bus_wdata;
  logic [NB_MPERIPHS-1:0][ADDR_WIDTH-1:0] s_mperiph_bus_add;
  logic [NB_MPERIPHS-1:0]                 s_mperiph_bus_req;
  logic [NB_MPERIPHS-1:0]                 s_mperiph_bus_wen;
  logic [NB_MPERIPHS-1:0][BE_WIDTH-1:0]   s_mperiph_bus_be;
  logic [NB_MPERIPHS-1:0]                 s_mperiph_bus_gnt  ;
  logic [NB_MPERIPHS-1:0]                 s_mperiph_bus_r_opc;
  logic [NB_MPERIPHS-1:0][DATA_WIDTH-1:0] s_mperiph_bus_r_rdata;
  logic [NB_MPERIPHS-1:0]                 s_mperiph_bus_r_valid;

  // DEMUX --> LOGARITHMIC INTERCONNECT BUS SIGNALS
  logic [NB_CORES+NB_HWACC_PORTS-1:0][DATA_WIDTH-1:0] s_core_tcdm_bus_wdata;
  logic [NB_CORES+NB_HWACC_PORTS-1:0][ADDR_WIDTH-1:0] s_core_tcdm_bus_add;
  logic [NB_CORES+NB_HWACC_PORTS-1:0]                 s_core_tcdm_bus_req;
  logic [NB_CORES+NB_HWACC_PORTS-1:0]                 s_core_tcdm_bus_wen;
  logic [NB_CORES+NB_HWACC_PORTS-1:0][BE_WIDTH-1:0]   s_core_tcdm_bus_be;
  logic [NB_CORES+NB_HWACC_PORTS-1:0]                 s_core_tcdm_bus_gnt;
  logic [NB_CORES+NB_HWACC_PORTS-1:0][DATA_WIDTH-1:0] s_core_tcdm_bus_r_rdata;
  logic [NB_CORES+NB_HWACC_PORTS-1:0]                 s_core_tcdm_bus_r_valid;

  // DEMUX -->  PERIPHERAL INTERCONNECT BUS SIGNALS
  logic [NB_CORES-1:0][ADDR_WIDTH-1:0] s_core_periph_bus_add;
  logic [NB_CORES-1:0]                 s_core_periph_bus_req;
  logic [NB_CORES-1:0][DATA_WIDTH-1:0] s_core_periph_bus_wdata;
  logic [NB_CORES-1:0]                 s_core_periph_bus_wen;
  logic [NB_CORES-1:0][5:0]            s_core_periph_bus_atop;
  logic [NB_CORES-1:0][BE_WIDTH-1:0]   s_core_periph_bus_be;
  logic [NB_CORES-1:0]                 s_core_periph_bus_gnt;
  logic [NB_CORES-1:0]                 s_core_periph_bus_r_opc;
  logic [NB_CORES-1:0]                 s_core_periph_bus_r_valid;
  logic [NB_CORES-1:0][DATA_WIDTH-1:0] s_core_periph_bus_r_rdata;

  // LOGARITHMIC INTERCONNECT --> Superbank MUX
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0][ADDR_MEM_WIDTH-1:0] s_tcdm_bus_sb_mux_add;
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0]                     s_tcdm_bus_sb_mux_req;
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0]                     s_tcdm_bus_sb_mux_gnt;
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0]                     s_tcdm_bus_sb_mux_wen;
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0][5:0]                s_tcdm_bus_sb_mux_atop;
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0][DATA_WIDTH-1:0]     s_tcdm_bus_sb_mux_wdata;
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0][BE_WIDTH-1:0]       s_tcdm_bus_sb_mux_be;
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0][DATA_WIDTH-1:0]     s_tcdm_bus_sb_mux_rdata;

  // Superbank MUX --> Amo Shims
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0][ADDR_MEM_WIDTH-1:0] s_sb_mux_amo_shim_add;
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0]                     s_sb_mux_amo_shim_req;
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0]                     s_sb_mux_amo_shim_gnt;
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0]                     s_sb_mux_amo_shim_wen;
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0][5:0]                s_sb_mux_amo_shim_atop;
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0][DATA_WIDTH-1:0]     s_sb_mux_amo_shim_wdata;
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0][BE_WIDTH-1:0]       s_sb_mux_amo_shim_be;
  logic [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0][DATA_WIDTH-1:0]     s_sb_mux_amo_shim_rdata;

  // DMA Superbank Decoder -> Superbank MUX
  logic [NB_SUPERBANKS-1:0]                        s_decoder_sb_a_mux_req;
  logic [NB_SUPERBANKS-1:0]                        s_decoder_sb_a_mux_gnt;
  logic [NB_SUPERBANKS-1:0][ADDR_MEM_WIDTH-1:0]    s_decoder_sb_a_mux_add;
  logic [NB_SUPERBANKS-1:0][5:0]                   s_decoder_sb_a_mux_amo;
  logic [NB_SUPERBANKS-1:0]                        s_decoder_sb_a_mux_wen;
  logic [NB_SUPERBANKS-1:0][DMA_DATA_WIDTH-1:0]    s_decoder_sb_a_mux_wdata;
  logic [NB_SUPERBANKS-1:0][DMA_DATA_WIDTH/8-1:0]  s_decoder_sb_a_mux_be;
  logic [NB_SUPERBANKS-1:0][DMA_DATA_WIDTH-1:0]    s_decoder_sb_a_mux_rdata;

  // DMA Superbank Decoder -> Superbank MUX
  logic [NB_SUPERBANKS-1:0]                        s_decoder_sb_b_mux_req;
  logic [NB_SUPERBANKS-1:0]                        s_decoder_sb_b_mux_gnt;
  logic [NB_SUPERBANKS-1:0][ADDR_MEM_WIDTH-1:0]    s_decoder_sb_b_mux_add;
  logic [NB_SUPERBANKS-1:0][5:0]                   s_decoder_sb_b_mux_amo;
  logic [NB_SUPERBANKS-1:0]                        s_decoder_sb_b_mux_wen;
  logic [NB_SUPERBANKS-1:0][DMA_DATA_WIDTH-1:0]    s_decoder_sb_b_mux_wdata;
  logic [NB_SUPERBANKS-1:0][DMA_DATA_WIDTH/8-1:0]  s_decoder_sb_b_mux_be;
  logic [NB_SUPERBANKS-1:0][DMA_DATA_WIDTH-1:0]    s_decoder_sb_b_mux_rdata;

  // DMA -> DMA Superbank Decoder a
  logic                        s_dma_decoder_a_req;
  logic                        s_dma_decoder_a_gnt;
  logic [DMA_ADDR_WIDTH-1:0]   s_dma_decoder_a_add;
  logic [5:0]                  s_dma_decoder_a_amo;
  logic                        s_dma_decoder_a_wen;
  logic [DMA_DATA_WIDTH-1:0]   s_dma_decoder_a_wdata;
  logic [DMA_DATA_WIDTH/8-1:0] s_dma_decoder_a_be;
  logic [DMA_DATA_WIDTH-1:0]   s_dma_decoder_a_rdata;

  // DMA -> DMA Superbank Decoder b
  logic                        s_dma_decoder_b_req;
  logic                        s_dma_decoder_b_gnt;
  logic [DMA_ADDR_WIDTH-1:0]   s_dma_decoder_b_add;
  logic [5:0]                  s_dma_decoder_b_amo;
  logic                        s_dma_decoder_b_wen;
  logic [DMA_DATA_WIDTH-1:0]   s_dma_decoder_b_wdata;
  logic [DMA_DATA_WIDTH/8-1:0] s_dma_decoder_b_be;
  logic [DMA_DATA_WIDTH-1:0]   s_dma_decoder_b_rdata;

  // PERIPHERAL INTERCONNECT INTERCONNECT --> SLAVE PERIPHERALS BUS SIGNALS
  logic [NB_SPERIPHS-1:0][DATA_WIDTH-1:0]           s_speriph_bus_wdata;
  logic [NB_SPERIPHS-1:0][ADDR_WIDTH-1:0]           s_speriph_bus_add;
  logic [NB_SPERIPHS-1:0]                           s_speriph_bus_req;
  logic [NB_SPERIPHS-1:0]                           s_speriph_bus_wen;
  logic [NB_SPERIPHS-1:0][5:0]                      s_speriph_bus_atop;
  logic [NB_SPERIPHS-1:0][BE_WIDTH-1:0]             s_speriph_bus_be;
  logic [NB_SPERIPHS-1:0][NB_CORES+NB_MPERIPHS-1:0] s_speriph_bus_id;
  logic [NB_SPERIPHS-1:0]                           s_speriph_bus_gnt  ;
  logic [NB_SPERIPHS-1:0]                           s_speriph_bus_r_opc;
  logic [NB_SPERIPHS-1:0][NB_CORES+NB_MPERIPHS-1:0] s_speriph_bus_r_id;
  logic [NB_SPERIPHS-1:0][DATA_WIDTH-1:0]           s_speriph_bus_r_rdata;
  logic [NB_SPERIPHS-1:0]                           s_speriph_bus_r_valid;

  //********************************************************
  //****** BINDING INTERFACES TO INTERNAL BUS SINGALS ******
  //********************************************************
  generate
    for (genvar i=0; i<NB_CORES; i++) begin : CORE_PERIPH_BIND
      assign s_core_periph_bus_add[i]      =  core_periph_slave[i].add;
      assign s_core_periph_bus_req[i]      =  core_periph_slave[i].req;
      assign s_core_periph_bus_wdata[i]    =  core_periph_slave[i].wdata;
      assign s_core_periph_bus_wen[i]      =  core_periph_slave[i].wen;
      assign s_core_periph_bus_atop[i]     =  core_periph_slave_atop[i];
      assign s_core_periph_bus_be[i]       =  core_periph_slave[i].be;

      assign core_periph_slave[i].gnt      =  s_core_periph_bus_gnt[i];
      assign core_periph_slave[i].r_opc    =  s_core_periph_bus_r_opc[i];
      assign core_periph_slave[i].r_valid  =  s_core_periph_bus_r_valid[i];
      assign core_periph_slave[i].r_rdata  =  s_core_periph_bus_r_rdata[i];
    end // block: CORE_PERIPH_BIND
  endgenerate

  generate
    for (genvar i=0; i<NB_CORES+NB_HWACC_PORTS; i++) begin : CORE_TCDM_BIND
      assign s_core_tcdm_bus_add[i]      = core_tcdm_slave[i].add;
      assign s_core_tcdm_bus_req[i]      = core_tcdm_slave[i].req;
      assign s_core_tcdm_bus_wdata[i]    = core_tcdm_slave[i].wdata;
      assign s_core_tcdm_bus_wen[i]      = core_tcdm_slave[i].wen;
      assign s_core_tcdm_bus_be[i]       = core_tcdm_slave[i].be;

      assign core_tcdm_slave[i].gnt      = s_core_tcdm_bus_gnt[i];
      assign core_tcdm_slave[i].r_valid  = s_core_tcdm_bus_r_valid[i];
      assign core_tcdm_slave[i].r_rdata  = s_core_tcdm_bus_r_rdata[i];
    end // block: CORE_TCDM_BIND
  endgenerate

  generate
    for (genvar i=0; i<NB_EXT; i++) begin : AXI2MEM_BIND
      assign s_dma_bus_add[i]      = ext_slave[i].add;
      assign s_dma_bus_req[i]      = ext_slave[i].req;
      assign s_dma_bus_wdata[i]    = ext_slave[i].wdata;
      assign s_dma_bus_wen[i]      = ext_slave[i].wen;
      assign s_dma_bus_be[i]       = ext_slave[i].be;

      assign ext_slave[i].gnt      = s_dma_bus_gnt[i];
      assign ext_slave[i].r_valid  = s_dma_bus_r_valid[i];
      assign ext_slave[i].r_rdata  = s_dma_bus_r_rdata[i];
    end
  endgenerate

  generate
    for (genvar i=0; i<NB_DMAS; i++) begin : DMAS_BIND
      assign s_dma_bus_add[NB_EXT+i]    = dma_slave[i].add;
      assign s_dma_bus_req[NB_EXT+i]    = dma_slave[i].req;
      assign s_dma_bus_wdata[NB_EXT+i]  = dma_slave[i].wdata;
      assign s_dma_bus_wen[NB_EXT+i]    = dma_slave[i].wen;
      assign s_dma_bus_be[NB_EXT+i]     = dma_slave[i].be;

      assign dma_slave[i].gnt      = s_dma_bus_gnt[NB_EXT+i];
      assign dma_slave[i].r_valid  = s_dma_bus_r_valid[NB_EXT+i];
      assign dma_slave[i].r_rdata  = s_dma_bus_r_rdata[NB_EXT+i];
    end
  endgenerate

  generate
    for (genvar i=0; i<NB_MPERIPHS; i++) begin : MPERIPHS_BIND
      assign s_mperiph_bus_add[i]      = mperiph_slave[i].add;
      assign s_mperiph_bus_req[i]      = mperiph_slave[i].req;
      assign s_mperiph_bus_wdata[i]    = mperiph_slave[i].wdata;
      assign s_mperiph_bus_wen[i]      = mperiph_slave[i].wen;
      assign s_mperiph_bus_be[i]       = mperiph_slave[i].be;

      assign mperiph_slave[i].gnt      = s_mperiph_bus_gnt[i];
      assign mperiph_slave[i].r_opc    = s_mperiph_bus_r_opc[i];
      assign mperiph_slave[i].r_valid  = s_mperiph_bus_r_valid[i];
      assign mperiph_slave[i].r_rdata  = s_mperiph_bus_r_rdata[i];
    end // block: MPERIPHS_BIND
  endgenerate

  generate
    for (genvar i=0; i<NB_SPERIPHS; i++) begin : SPERIPHS_BIND
      assign speriph_master[i].add       = s_speriph_bus_add[i];
      assign speriph_master[i].req       = s_speriph_bus_req[i];
      assign speriph_master[i].wdata     = s_speriph_bus_wdata[i];
      assign speriph_master[i].wen       = s_speriph_bus_wen[i];
      assign speriph_master_atop[i]      = s_speriph_bus_atop[i];
      assign speriph_master[i].be        = s_speriph_bus_be[i];
      assign speriph_master[i].id        = s_speriph_bus_id[i];

      assign s_speriph_bus_gnt[i]        = speriph_master[i].gnt;
      assign s_speriph_bus_r_id[i]       = speriph_master[i].r_id;
      assign s_speriph_bus_r_opc[i]      = speriph_master[i].r_opc;
      assign s_speriph_bus_r_valid[i]    = speriph_master[i].r_valid;
      assign s_speriph_bus_r_rdata[i]    = speriph_master[i].r_rdata;
    end // block: SPERIPHS_BIND
  endgenerate

  localparam NUM_TCDM_ICONN_IN = NB_CORES + NB_HWACC_PORTS + NB_DMAS + NB_EXT;
  typedef struct packed {
    logic [DATA_WIDTH-1:0]  data;
    logic [5:0]             atop;
  } tcdm_data_t;
  tcdm_data_t [NUM_TCDM_ICONN_IN-1:0]                      iconn_inp_wdata, iconn_inp_rdata;
  tcdm_data_t [NB_SUPERBANKS-1:0][BANKS_PER_SUPERBANK-1:0] iconn_oup_wdata, iconn_oup_rdata;
  tcdm_interconnect #(
    .NumIn        ( NUM_TCDM_ICONN_IN           ),
    .NumOut       ( NB_TCDM_BANKS               ),
    .AddrWidth    ( ADDR_WIDTH                  ),
    .DataWidth    ( $bits(tcdm_data_t)          ),
    .ByteOffWidth ( $clog2(DATA_WIDTH-1)-3      ), // determine byte offset from real data width
    .AddrMemWidth ( ADDR_MEM_WIDTH              ),
    .WriteRespOn  ( 1                           ),
    .RespLat      ( 1                           ),
    .Topology     ( tcdm_interconnect_pkg::LIC  )
  ) i_tcdm_interconnect (
    .clk_i,
    .rst_ni,

    .req_i    ( { s_dma_bus_req,      s_core_tcdm_bus_req}      ),
    .add_i    ( { s_dma_bus_add,      s_core_tcdm_bus_add}      ),
    .wen_i    ( { s_dma_bus_wen,      s_core_tcdm_bus_wen}      ),
    .wdata_i  ( iconn_inp_wdata                                 ),
    .be_i     ( { s_dma_bus_be,       s_core_tcdm_bus_be}       ),
    .gnt_o    ( { s_dma_bus_gnt,      s_core_tcdm_bus_gnt}      ),
    .vld_o    ( { s_dma_bus_r_valid,  s_core_tcdm_bus_r_valid}  ),
    .rdata_o  ( iconn_inp_rdata                                 ),

    .req_o    ( s_tcdm_bus_sb_mux_req   ),
    .gnt_i    ( s_tcdm_bus_sb_mux_gnt   ),
    .add_o    ( s_tcdm_bus_sb_mux_add   ),
    .wen_o    ( s_tcdm_bus_sb_mux_wen   ),
    .wdata_o  ( iconn_oup_wdata           ),
    .be_o     ( s_tcdm_bus_sb_mux_be    ),
    .rdata_i  ( iconn_oup_rdata           )
  );
  // tcdm output side
  for (genvar i = 0; i < NB_SUPERBANKS; i++) begin : gen_amo_split_sb
    for (genvar j = 0; j < BANKS_PER_SUPERBANK; j++) begin : gen_amo_split_sb
      tcdm_data_t rdata, wdata;
      assign iconn_oup_rdata         [i][j] = rdata;
      assign rdata.data                     = s_tcdm_bus_sb_mux_rdata [i][j];
      assign rdata.atop                     = 6'h00;
      assign wdata                          = iconn_oup_wdata [i][j];
      assign s_tcdm_bus_sb_mux_wdata [i][j] = wdata.data;
      assign s_tcdm_bus_sb_mux_atop  [i][j] = wdata.atop;
    end
  end
  // tcdm input side
  for (genvar i = 0; i < NUM_TCDM_ICONN_IN; i++) begin : gen_iconn_pack_inp_data
    if (i < NB_CORES + NB_HWACC_PORTS) begin
      assign iconn_inp_wdata[i].data = s_core_tcdm_bus_wdata[i];
      assign s_core_tcdm_bus_r_rdata[i] = iconn_inp_rdata[i].data;
    end else begin
      assign iconn_inp_wdata[i].data = s_dma_bus_wdata[i - (NB_CORES + NB_HWACC_PORTS)];
      assign s_dma_bus_r_rdata[i - (NB_CORES + NB_HWACC_PORTS)] = iconn_inp_rdata[i].data;
    end
    if (i < NB_CORES) begin
      assign iconn_inp_wdata[i].atop = core_tcdm_slave_atop[i];
    end else if (i < NB_CORES + NB_EXT) begin
      assign iconn_inp_wdata[i].atop = ext_slave_atop[i-NB_CORES];
    end else begin
      assign iconn_inp_wdata[i].atop = '0;
    end
  end

  // performance counter for tcdm
  //pragma translate_off
  `ifndef SYNTHESYS
  `ifndef VERILATOR

  logic [$clog2(NB_TCDM_BANKS):0] tcdm_conflicts, mem_conflicts;
  logic [$clog2(NB_SUPERBANKS):0] sb_a_conflicts, sb_b_conflicts;
  logic [$clog2(NB_CORES):0]      core_conflicts;

  logic [$clog2(NB_TCDM_BANKS):0] tcdm_accesses, mem_accesses;
  logic [$clog2(NB_SUPERBANKS):0] sb_a_accesses, sb_b_accesses;
  logic [$clog2(NB_CORES):0]      core_accesses;

  logic [63:0] tcdm_conflicts_q, mem_conflicts_q, sb_a_conflicts_q, sb_b_conflicts_q, tcdm_accesses_q, mem_accesses_q, sb_a_accesses_q, sb_b_accesses_q, core_conflicts_q, core_accesses_q;

  popcount #(.INPUT_WIDTH(NB_TCDM_BANKS))  i_popcount_0 (.data_i(s_tcdm_bus_sb_mux_req  & ~s_tcdm_bus_sb_mux_gnt),  .popcount_o(tcdm_conflicts));
  popcount #(.INPUT_WIDTH(NB_SUPERBANKS))  i_popcount_1 (.data_i(s_decoder_sb_a_mux_req & ~s_decoder_sb_a_mux_gnt), .popcount_o(sb_a_conflicts));
  popcount #(.INPUT_WIDTH(NB_SUPERBANKS))  i_popcount_2 (.data_i(s_decoder_sb_b_mux_req & ~s_decoder_sb_b_mux_gnt), .popcount_o(sb_b_conflicts));
  popcount #(.INPUT_WIDTH(NB_TCDM_BANKS))  i_popcount_3 (.data_i(s_sb_mux_amo_shim_req  & ~s_sb_mux_amo_shim_gnt),  .popcount_o(mem_conflicts));

  popcount #(.INPUT_WIDTH(NB_TCDM_BANKS))  i_popcount_4 (.data_i(s_tcdm_bus_sb_mux_req  &  s_tcdm_bus_sb_mux_gnt), .popcount_o(tcdm_accesses));
  popcount #(.INPUT_WIDTH(NB_SUPERBANKS))  i_popcount_5 (.data_i(s_decoder_sb_a_mux_req &  s_decoder_sb_a_mux_gnt), .popcount_o(sb_a_accesses));
  popcount #(.INPUT_WIDTH(NB_SUPERBANKS))  i_popcount_6 (.data_i(s_decoder_sb_b_mux_req &  s_decoder_sb_b_mux_gnt), .popcount_o(sb_b_accesses));
  popcount #(.INPUT_WIDTH(NB_TCDM_BANKS))  i_popcount_7 (.data_i(s_sb_mux_amo_shim_req  &  s_sb_mux_amo_shim_gnt), .popcount_o(mem_accesses));

  popcount #(.INPUT_WIDTH(NB_CORES))       i_popcount_8 (.data_i(s_core_tcdm_bus_req    & ~s_core_tcdm_bus_gnt), .popcount_o(core_conflicts));
  popcount #(.INPUT_WIDTH(NB_CORES))       i_popcount_9 (.data_i(s_core_tcdm_bus_req    &  s_core_tcdm_bus_gnt), .popcount_o(core_accesses));

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_counters
    if(~rst_ni) begin
      tcdm_conflicts_q <= '0;
      mem_conflicts_q  <= '0;
      sb_a_conflicts_q <= '0;
      sb_b_conflicts_q <= '0;
      tcdm_accesses_q  <= '0;
      mem_accesses_q   <= '0;
      sb_a_accesses_q  <= '0;
      sb_b_accesses_q  <= '0;
      core_conflicts_q <= '0;
      core_accesses_q  <= '0;
    end else begin
      tcdm_conflicts_q <= tcdm_conflicts_q + tcdm_conflicts;
      mem_conflicts_q  <= mem_conflicts_q  + mem_conflicts;
      sb_a_conflicts_q <= sb_a_conflicts_q + sb_a_conflicts;
      sb_b_conflicts_q <= sb_b_conflicts_q + sb_b_conflicts;
      tcdm_accesses_q  <= tcdm_accesses_q  + tcdm_accesses;
      mem_accesses_q   <= mem_accesses_q   + mem_accesses;
      sb_a_accesses_q  <= sb_a_accesses_q  + sb_a_accesses;
      sb_b_accesses_q  <= sb_b_accesses_q  + sb_b_accesses;
      core_conflicts_q <= core_conflicts_q + core_conflicts;
      core_accesses_q  <= core_accesses_q  + core_accesses;
    end
  end
  /*
  initial begin
    forever begin
      $display("%m: %d core conflicts: %f%% - interconnect conflicts: %f%% - superbank a conflicts: %f%% - superbank b conflicts: %f%% - memory conflicts: %f%%",
                  $time(),
                  100.0 * savediv($itor(core_conflicts_q), ($itor(core_accesses_q) + $itor(core_conflicts_q))),
                  100.0 * savediv($itor(tcdm_conflicts_q), ($itor(tcdm_accesses_q) + $itor(tcdm_conflicts_q))),
                  100.0 * savediv($itor(sb_a_conflicts_q), ($itor(sb_a_accesses_q) + $itor(sb_a_conflicts_q))),
                  100.0 * savediv($itor(sb_b_conflicts_q), ($itor(sb_b_accesses_q) + $itor(sb_b_conflicts_q))),
                  100.0 * savediv($itor(mem_conflicts_q) , ($itor(mem_accesses_q)  + $itor(mem_conflicts_q)))
               );
      repeat(20) begin
        @(posedge clk_i);
      end
    end
  end
  */
  `endif
  `endif
  //pragma translate_on

  // connect to DMA a
  assign s_dma_decoder_a_req             = s_wide_dma_a_superbanks.req;
  assign s_dma_decoder_a_add             = s_wide_dma_a_superbanks.add;
  assign s_dma_decoder_a_amo             = '0;
  assign s_dma_decoder_a_wen             = s_wide_dma_a_superbanks.wen;
  assign s_dma_decoder_a_wdata           = s_wide_dma_a_superbanks.wdata;
  assign s_dma_decoder_a_be              = s_wide_dma_a_superbanks.be;
  assign s_wide_dma_a_superbanks.gnt     = s_dma_decoder_a_gnt;
  assign s_wide_dma_a_superbanks.r_rdata = s_dma_decoder_a_rdata;
  assign s_wide_dma_a_superbanks.r_opc   = '0;
  assign s_wide_dma_a_superbanks.r_valid = '0;

  // connect to DMA b
  assign s_dma_decoder_b_req             = s_wide_dma_b_superbanks.req;
  assign s_dma_decoder_b_add             = s_wide_dma_b_superbanks.add;
  assign s_dma_decoder_b_amo             = '0;
  assign s_dma_decoder_b_wen             = s_wide_dma_b_superbanks.wen;
  assign s_dma_decoder_b_wdata           = s_wide_dma_b_superbanks.wdata;
  assign s_dma_decoder_b_be              = s_wide_dma_b_superbanks.be;
  assign s_wide_dma_b_superbanks.gnt     = s_dma_decoder_b_gnt;
  assign s_wide_dma_b_superbanks.r_rdata = s_dma_decoder_b_rdata;
  assign s_wide_dma_b_superbanks.r_opc   = '0;
  assign s_wide_dma_b_superbanks.r_valid = '0;

  // DMA Superbank address decoder a
  // only needed if we have more than one SB!
  superbank_addr_decoder #(
    .TCDMAddrWidth      ( ADDR_MEM_WIDTH      ),
    .DMAAddrWidth       ( DMA_ADDR_WIDTH      ),
    .BanksPerSuperbank  ( BANKS_PER_SUPERBANK ),
    .NrSuperBanks       ( NB_SUPERBANKS       ),
    .DMADataWidth       ( DMA_DATA_WIDTH      ),
    .AmoWidth           ( 6                   ),
    .MemoryLatency      ( 1                   )
  ) i_superbank_addr_decoder_a (
    .clk_i              ( clk_i                    ),
    .rst_i              ( ~rst_ni                  ),
    .dma_req_i          ( s_dma_decoder_a_req      ),
    .dma_gnt_o          ( s_dma_decoder_a_gnt      ),
    .dma_add_i          ( s_dma_decoder_a_add      ),
    .dma_amo_i          ( s_dma_decoder_a_amo      ),
    .dma_wen_i          ( s_dma_decoder_a_wen      ),
    .dma_wdata_i        ( s_dma_decoder_a_wdata    ),
    .dma_be_i           ( s_dma_decoder_a_be       ),
    .dma_rdata_o        ( s_dma_decoder_a_rdata    ),
    .super_bank_req_o   ( s_decoder_sb_a_mux_req   ),
    .super_bank_gnt_i   ( s_decoder_sb_a_mux_gnt   ),
    .super_bank_add_o   ( s_decoder_sb_a_mux_add   ),
    .super_bank_amo_o   ( s_decoder_sb_a_mux_amo   ),
    .super_bank_wen_o   ( s_decoder_sb_a_mux_wen   ),
    .super_bank_wdata_o ( s_decoder_sb_a_mux_wdata ),
    .super_bank_be_o    ( s_decoder_sb_a_mux_be    ),
    .super_bank_rdata_i ( s_decoder_sb_a_mux_rdata )
  );

  // DMA Superbank address decoder b
  // only needed if we have more than one SB!
  superbank_addr_decoder #(
    .TCDMAddrWidth      ( ADDR_MEM_WIDTH      ),
    .DMAAddrWidth       ( DMA_ADDR_WIDTH      ),
    .BanksPerSuperbank  ( BANKS_PER_SUPERBANK ),
    .NrSuperBanks       ( NB_SUPERBANKS       ),
    .DMADataWidth       ( DMA_DATA_WIDTH      ),
    .AmoWidth           ( 6                   ),
    .MemoryLatency      ( 1                   )
  ) i_superbank_addr_decoder_b (
    .clk_i              ( clk_i                    ),
    .rst_i              ( ~rst_ni                  ),
    .dma_req_i          ( s_dma_decoder_b_req      ),
    .dma_gnt_o          ( s_dma_decoder_b_gnt      ),
    .dma_add_i          ( s_dma_decoder_b_add      ),
    .dma_amo_i          ( s_dma_decoder_b_amo      ),
    .dma_wen_i          ( s_dma_decoder_b_wen      ),
    .dma_wdata_i        ( s_dma_decoder_b_wdata    ),
    .dma_be_i           ( s_dma_decoder_b_be       ),
    .dma_rdata_o        ( s_dma_decoder_b_rdata    ),
    .super_bank_req_o   ( s_decoder_sb_b_mux_req   ),
    .super_bank_gnt_i   ( s_decoder_sb_b_mux_gnt   ),
    .super_bank_add_o   ( s_decoder_sb_b_mux_add   ),
    .super_bank_amo_o   ( s_decoder_sb_b_mux_amo   ),
    .super_bank_wen_o   ( s_decoder_sb_b_mux_wen   ),
    .super_bank_wdata_o ( s_decoder_sb_b_mux_wdata ),
    .super_bank_be_o    ( s_decoder_sb_b_mux_be    ),
    .super_bank_rdata_i ( s_decoder_sb_b_mux_rdata )
  );

  for (genvar j = 0; j < NB_SUPERBANKS; j++) begin : gen_superbank
    // initial $display("Generate Superbank %2d", j);

    // one multiplexer per superbank
    tcdm_superbank_mux #(
      .AddrMemWidth       ( ADDR_MEM_WIDTH       ),
      .BanksPerSuperbank  ( BANKS_PER_SUPERBANK  ),
      .DMADataWidth       ( DMA_DATA_WIDTH       ),
      .DataWidth          ( DATA_WIDTH           ),
      .AmoWidth           ( 6                    )
    ) i_tcdm_superbank_mux (
      .clk_i          ( clk_i                          ),
      .rst_i          ( ~rst_ni                        ),
      // tcdm interconnect (one superbank)
      .ic_req_i       ( s_tcdm_bus_sb_mux_req   [j]    ),
      .ic_gnt_o       ( s_tcdm_bus_sb_mux_gnt   [j]    ),
      .ic_add_i       ( s_tcdm_bus_sb_mux_add   [j]    ),
      .ic_amo_i       ( s_tcdm_bus_sb_mux_atop  [j]    ),
      .ic_wen_i       ( s_tcdm_bus_sb_mux_wen   [j]    ),
      .ic_wdata_i     ( s_tcdm_bus_sb_mux_wdata [j]    ),
      .ic_be_i        ( s_tcdm_bus_sb_mux_be    [j]    ),
      .ic_rdata_o     ( s_tcdm_bus_sb_mux_rdata [j]    ),
      // dma port a (one superbank)
      .dma_a_req_i    ( s_decoder_sb_a_mux_req    [j]  ),
      .dma_a_gnt_o    ( s_decoder_sb_a_mux_gnt    [j]  ),
      .dma_a_add_i    ( s_decoder_sb_a_mux_add    [j]  ),
      .dma_a_amo_i    ( s_decoder_sb_a_mux_amo    [j]  ),
      .dma_a_wen_i    (~s_decoder_sb_a_mux_wen    [j]  ),
      .dma_a_wdata_i  ( s_decoder_sb_a_mux_wdata  [j]  ),
      .dma_a_be_i     ( s_decoder_sb_a_mux_be     [j]  ),
      .dma_a_rdata_o  ( s_decoder_sb_a_mux_rdata  [j]  ),
      // dma port b (one superbank)
      .dma_b_req_i    ( s_decoder_sb_b_mux_req    [j]  ),
      .dma_b_gnt_o    ( s_decoder_sb_b_mux_gnt    [j]  ),
      .dma_b_add_i    ( s_decoder_sb_b_mux_add    [j]  ),
      .dma_b_amo_i    ( s_decoder_sb_b_mux_amo    [j]  ),
      .dma_b_wen_i    (~s_decoder_sb_b_mux_wen    [j]  ),
      .dma_b_wdata_i  ( s_decoder_sb_b_mux_wdata  [j]  ),
      .dma_b_be_i     ( s_decoder_sb_b_mux_be     [j]  ),
      .dma_b_rdata_o  ( s_decoder_sb_b_mux_rdata  [j]  ),
      // to amo shims
      .amo_req_o      ( s_sb_mux_amo_shim_req   [j]    ),
      .amo_gnt_i      ( s_sb_mux_amo_shim_gnt   [j]    ),
      .amo_add_o      ( s_sb_mux_amo_shim_add   [j]    ),
      .amo_amo_o      ( s_sb_mux_amo_shim_atop  [j]    ),
      .amo_wen_o      ( s_sb_mux_amo_shim_wen   [j]    ),
      .amo_wdata_o    ( s_sb_mux_amo_shim_wdata [j]    ),
      .amo_be_o       ( s_sb_mux_amo_shim_be    [j]    ),
      .amo_rdata_i    ( s_sb_mux_amo_shim_rdata [j]    ),
      // select DMA
      .sel_dma_a_i    ( s_decoder_sb_a_mux_req    [j]  ),
      .sel_dma_b_i    ( s_decoder_sb_b_mux_req    [j]  )
    );

    for (genvar k = 0; k < BANKS_PER_SUPERBANK; k++) begin : gen_amo_shim
      localparam i = j * BANKS_PER_SUPERBANK + k;
      // initial $display(" -> Generate Amo Shim for Bank %2d (%2d-%2d)", i, j, k);
      // Map ATOPs by RI5CYs to AMOs.
      logic [DATA_WIDTH-1:0] data;
      logic [5:0] atop;
      logic [3:0] amo;
      assign atop = s_sb_mux_amo_shim_atop[j][k];
      always_comb begin
        data = s_sb_mux_amo_shim_wdata[j][k];
        if (atop[5]) begin
          unique casez (atop[4:0])
            riscv_defines::AMO_ADD:   amo = 4'h2;
            riscv_defines::AMO_SWAP:  amo = 4'h1;
            riscv_defines::AMO_LR:    $error("Unsupported LR on L1!");
            riscv_defines::AMO_SC:    $error("Unsupported SC on L1!");
            default: begin
              assert (atop[1:0] == '0) else $error("Illegal AMO!");
              unique case (atop[4:2])
                riscv_defines::AMO_XOR[4:2]:  amo = 4'h5;
                riscv_defines::AMO_OR[4:2]:   amo = 4'h4;
                riscv_defines::AMO_AND[4:2]:  amo = 4'h3;
                riscv_defines::AMO_MIN[4:2]:  amo = 4'h8;
                riscv_defines::AMO_MAX[4:2]:  amo = 4'h6;
                riscv_defines::AMO_MINU[4:2]: amo = 4'h9;
                riscv_defines::AMO_MAXU[4:2]: amo = 4'h7;
              endcase
            end
          endcase
        end else begin
          amo = 4'h0; // AMONone
        end
      end
      logic write_enable;
      logic [ADDR_MEM_WIDTH+2-1:0] addr;
      amo_shim #(
        .AddrMemWidth (ADDR_MEM_WIDTH+2),
        .DataWidth    (DATA_WIDTH)
      ) i_amo_shim (
        .clk_i,
        .rst_ni,

        .in_req_i       ( s_sb_mux_amo_shim_req[j][k]         ),
        .in_gnt_o       ( s_sb_mux_amo_shim_gnt[j][k]         ),
        .in_add_i       ({s_sb_mux_amo_shim_add[j][k], 2'b00} ),
        .in_amo_i       ( amo                                 ),
        .in_wen_i       (~s_sb_mux_amo_shim_wen[j][k]         ), // 0 = write, 1 = read
        .in_wdata_i     ( data                                ),
        .in_be_i        ( s_sb_mux_amo_shim_be[j][k]          ),
        .in_rdata_o     ( s_sb_mux_amo_shim_rdata [j][k]      ),

        .out_req_o      ( tcdm_sram_master[i].req             ),
        .out_add_o      ( addr                                ),
        .out_wen_o      ( write_enable                        ),
        .out_wdata_o    ( tcdm_sram_master[i].wdata           ),
        .out_be_o       ( tcdm_sram_master[i].be              ),
        .out_rdata_i    ( tcdm_sram_master[i].rdata           ),
        .dma_access_i   ( s_decoder_sb_a_mux_req[j] | s_decoder_sb_b_mux_req[j] ),
        .amo_conflict_o ( )
      );
      always_comb begin
        tcdm_sram_master[i].add = '0;
        tcdm_sram_master[i].add[ADDR_MEM_WIDTH-1:0] = addr[ADDR_MEM_WIDTH+2-1:2];
      end
      assign tcdm_sram_master[i].wen = ~write_enable;
    end // gen_amo_shim
  end // gen_superbank

  // peripheral logarithmic interconnect
  XBAR_PE #(
    .N_CH0              ( NB_CORES             ),
    .N_CH1              ( NB_MPERIPHS          ),
    .N_SLAVE            ( NB_SPERIPHS          ),
    .ID_WIDTH           ( NB_CORES+NB_MPERIPHS ),
    .PE_LSB             ( 0                    ),
    .PE_MSB             ( ADDR_WIDTH-1         ),
    .LOG_CLUSTER        ( LOG_CLUSTER          ),
    .ADDR_WIDTH         ( ADDR_WIDTH           ),
    .DATA_WIDTH         ( DATA_WIDTH           ),
    .BE_WIDTH           ( BE_WIDTH             ),
    .PE_ROUTING_LSB     ( PE_ROUTING_LSB       ),
    .PE_ROUTING_MSB     ( PE_ROUTING_MSB       ),
    .CLUSTER_ALIAS      ( CLUSTER_ALIAS        ),
    .CLUSTER_ALIAS_BASE ( CLUSTER_ALIAS_BASE   )
  ) xbar_pe_inst (
    .clk              ( clk_i                                                   ),
    .rst_n            ( rst_ni                                                  ),
    .CLUSTER_ID       ( 5'b00000                                                ),
    .data_req_i       ( {s_mperiph_bus_req,         s_core_periph_bus_req}      ),
    .data_add_i       ( {s_mperiph_bus_add,         s_core_periph_bus_add}      ),
    .data_wen_i       ( {s_mperiph_bus_wen,         s_core_periph_bus_wen}      ),
    .data_atop_i      ( {{NB_MPERIPHS{6'b000000}},  s_core_periph_bus_atop}     ),
    .data_wdata_i     ( {s_mperiph_bus_wdata,       s_core_periph_bus_wdata}    ),
    .data_be_i        ( {s_mperiph_bus_be,          s_core_periph_bus_be}       ),
    .data_gnt_o       ( {s_mperiph_bus_gnt,         s_core_periph_bus_gnt}      ),
    .data_r_valid_o   ( {s_mperiph_bus_r_valid,     s_core_periph_bus_r_valid}  ),
    .data_r_rdata_o   ( {s_mperiph_bus_r_rdata,     s_core_periph_bus_r_rdata}  ),
    .data_r_opc_o     ( {s_mperiph_bus_r_opc,       s_core_periph_bus_r_opc}    ),
    .data_req_o       ( s_speriph_bus_req                                       ),
    .data_add_o       ( s_speriph_bus_add                                       ),
    .data_wen_o       ( s_speriph_bus_wen                                       ),
    .data_atop_o      ( s_speriph_bus_atop                                      ),
    .data_wdata_o     ( s_speriph_bus_wdata                                     ),
    .data_be_o        ( s_speriph_bus_be                                        ),
    .data_ID_o        ( s_speriph_bus_id                                        ),
    .data_gnt_i       ( s_speriph_bus_gnt                                       ),
    .data_r_rdata_i   ( s_speriph_bus_r_rdata                                   ),
    .data_r_valid_i   ( s_speriph_bus_r_valid                                   ),
    .data_r_ID_i      ( s_speriph_bus_r_id                                      ),
    .data_r_opc_i     ( s_speriph_bus_r_opc                                     )
  );

endmodule
