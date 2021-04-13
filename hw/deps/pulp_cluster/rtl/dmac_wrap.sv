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
 * dmac_wrap.sv
 * Davide Rossi <davide.rossi@unibo.it>
 * Antonio Pullini <pullinia@iis.ee.ethz.ch>
 * Igor Loi <igor.loi@unibo.it>
 * Francesco Conti <fconti@iis.ee.ethz.ch>
 * Thomas Benz <tbenz@iis.ee.ethz.ch>
 */

`include "axi/assign.svh"
`include "axi/typedef.svh"

module dmac_wrap
#(
  parameter NB_CORES           = 4,
  parameter NB_OUTSND_BURSTS   = 8,
  parameter MCHAN_BURST_LENGTH = 256,
  parameter AXI_ADDR_WIDTH     = 32,
  parameter AXI_DATA_WIDTH     = 64,
  parameter AXI_USER_WIDTH     = 6,
  parameter AXI_ID_WIDTH       = 4,
  parameter PE_ID_WIDTH        = 1,
  parameter TCDM_ADD_WIDTH     = 13,
  parameter DATA_WIDTH         = 32,
  parameter ADDR_WIDTH         = 32,
  parameter BE_WIDTH           = DATA_WIDTH/8,
  parameter DMA_AXI_AW_WIDTH   = 32,
  parameter DMA_AXI_DW_WIDTH   = 512,
  parameter DMA_AXI_ID_WIDTH   = 4,
  parameter DMA_AXI_UW_WIDTH   = 4,
  parameter TF_REQ_FIFO_DEPTH  = 4,

  parameter type dma_transf_descr_t = logic
)
(
  input logic                      clk_i,
  input logic                      rst_ni,
  input logic                      test_mode_i,
  input logic [5:0]                cluster_id_i,
  XBAR_PERIPH_BUS.Slave            pe_ctrl_slave,
  XBAR_TCDM_BUS.Slave              ctrl_slave[NB_CORES-1:0],
  XBAR_TCDM_BUS.Master             tcdm_master[3:0],
  AXI_BUS.Master                   ext_master,
  AXI_BUS.Master                   s_wide_dma_soc,
  WIDE_DMA_TCDM_BUS.Master         s_wide_dma_superbanks,
  output logic [NB_CORES-1:0]      term_event_o,
  output logic [NB_CORES-1:0]      term_irq_o,
  output logic                     term_event_pe_o,
  output logic                     term_irq_pe_o,
  output logic                     busy_o,

  input  logic                     ext_dma_req_valid_i,
  output logic                     ext_dma_req_ready_o,
  input  dma_transf_descr_t        ext_dma_req_i,

  output logic                     ext_dma_rsp_valid_o,

  output logic [NB_CORES-1:0]      no_req_pending_o

);

  // CORE --> MCHAN CTRL INTERFACE BUS SIGNALS
  logic [NB_CORES-1:0][DATA_WIDTH-1:0] s_ctrl_bus_wdata;
  logic [NB_CORES-1:0][ADDR_WIDTH-1:0] s_ctrl_bus_add;
  logic [NB_CORES-1:0]                 s_ctrl_bus_req;
  logic [NB_CORES-1:0]                 s_ctrl_bus_wen;
  logic [NB_CORES-1:0][BE_WIDTH-1:0]   s_ctrl_bus_be;
  logic [NB_CORES-1:0]                 s_ctrl_bus_gnt;
  logic [NB_CORES-1:0][DATA_WIDTH-1:0] s_ctrl_bus_r_rdata;
  logic [NB_CORES-1:0]                 s_ctrl_bus_r_valid;

  // MCHAN TCDM INIT --> TCDM MEMORY BUS SIGNALS
  logic [3:0][DATA_WIDTH-1:0] s_tcdm_bus_wdata;
  logic [3:0][ADDR_WIDTH-1:0] s_tcdm_bus_add;
  logic [3:0]                 s_tcdm_bus_req;
  logic [3:0]                 s_tcdm_bus_wen;
  logic [3:0][BE_WIDTH-1:0]   s_tcdm_bus_be;
  logic [3:0]                 s_tcdm_bus_gnt;
  logic [3:0][DATA_WIDTH-1:0] s_tcdm_bus_r_rdata;
  logic [3:0]                 s_tcdm_bus_r_valid;

  generate
    for (genvar i=0; i<NB_CORES; i++) begin : CTRL_SLAVE_BIND
      assign s_ctrl_bus_add[i]     = ctrl_slave[i].add;
      assign s_ctrl_bus_req[i]     = ctrl_slave[i].req;
      assign s_ctrl_bus_wdata[i]   = ctrl_slave[i].wdata;
      assign s_ctrl_bus_wen[i]     = ctrl_slave[i].wen;
      assign s_ctrl_bus_be[i]      = ctrl_slave[i].be;

      assign ctrl_slave[i].gnt     = s_ctrl_bus_gnt[i];
      assign ctrl_slave[i].r_opc   = 'b0;
      assign ctrl_slave[i].r_valid = s_ctrl_bus_r_valid[i];
      assign ctrl_slave[i].r_rdata = s_ctrl_bus_r_rdata[i];
    end
  endgenerate

  generate
    for (genvar i=0; i<4; i++) begin : TCDM_MASTER_BIND
      assign tcdm_master[i].add      = s_tcdm_bus_add[i];
      assign tcdm_master[i].req      = s_tcdm_bus_req[i];
      assign tcdm_master[i].wdata    = s_tcdm_bus_wdata[i];
      assign tcdm_master[i].wen      = s_tcdm_bus_wen[i];
      assign tcdm_master[i].be       = s_tcdm_bus_be[i];

      assign s_tcdm_bus_gnt[i]       = tcdm_master[i].gnt;
      assign s_tcdm_bus_r_valid[i]   = tcdm_master[i].r_valid;
      assign s_tcdm_bus_r_rdata[i]   = tcdm_master[i].r_rdata;
    end
  endgenerate

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH  ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH  ),
    .AXI_ID_WIDTH   ( AXI_ID_WIDTH    ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH  )
  ) internal ();

  axi_serializer_intf #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH    ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
    .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH    ),
    .MAX_READ_TXNS  ( NB_OUTSND_BURSTS  ),
    .MAX_WRITE_TXNS ( NB_OUTSND_BURSTS  )
  ) i_serializer (
    .clk_i,
    .rst_ni,
    .slv    (internal),
    .mst    (ext_master)
  );

  // axi definition
  typedef logic [DMA_AXI_AW_WIDTH-1  :0] addr_t;
  typedef logic [DMA_AXI_DW_WIDTH-1  :0] data_t;
  typedef logic [DMA_AXI_ID_WIDTH-1  :0] id_oup_t;
  typedef logic [DMA_AXI_DW_WIDTH/8-1:0] strb_t;
  typedef logic [DMA_AXI_UW_WIDTH-1  :0] user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_oup_t, user_t);
  `AXI_TYPEDEF_W_CHAN_T (w_chan_t, data_t, strb_t, user_t);
  `AXI_TYPEDEF_B_CHAN_T (b_chan_t, id_oup_t, user_t);
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_oup_t, user_t);
  `AXI_TYPEDEF_R_CHAN_T (r_chan_t, data_t, id_oup_t, user_t);
  `AXI_TYPEDEF_REQ_T    (axi_dma_req_t, aw_chan_t, w_chan_t, ar_chan_t);
  `AXI_TYPEDEF_RESP_T   (axi_dma_resp_t, b_chan_t, r_chan_t);
  axi_dma_req_t   axi_dma_req, axi_dma_soc_req, axi_dma_tcdm_req, axi_dma_tcdm_r_req, axi_dma_tcdm_w_req;
  axi_dma_resp_t  axi_dma_res, axi_dma_soc_res, axi_dma_tcdm_res, axi_dma_tcdm_r_res, axi_dma_tcdm_w_res;

  // new axi dma
  pulp_cluster_frontend #(
    .NumCores       ( NB_CORES                             ),
    .PerifIdWidth   ( PE_ID_WIDTH                          ),
    .DmaAxiIdWidth  ( DMA_AXI_ID_WIDTH                     ),
    .DmaDataWidth   ( DMA_AXI_DW_WIDTH                     ),
    .DmaAddrWidth   ( DMA_AXI_AW_WIDTH                     ),
    .AxiAxReqDepth  ( 12                                   ), // TODO: tune me
    .TfReqFifoDepth ( TF_REQ_FIFO_DEPTH                    ), // TODO: tune me
    .axi_req_t      ( axi_dma_req_t                        ),
    .axi_res_t      ( axi_dma_resp_t                       ),
    .transf_descr_t ( dma_transf_descr_t                   )
  ) i_pulp_cluster_frontend (
    .clk_i                   ( clk_i                   ),
    .rst_ni                  ( rst_ni                  ),
    .cluster_id_i            ( cluster_id_i            ),
    .ctrl_pe_targ_req_i      ( pe_ctrl_slave.req       ),
    .ctrl_pe_targ_type_i     ( pe_ctrl_slave.wen       ),
    .ctrl_pe_targ_be_i       ( pe_ctrl_slave.be        ),
    .ctrl_pe_targ_add_i      ( pe_ctrl_slave.add       ),
    .ctrl_pe_targ_data_i     ( pe_ctrl_slave.wdata     ),
    .ctrl_pe_targ_id_i       ( pe_ctrl_slave.id        ),
    .ctrl_pe_targ_gnt_o      ( pe_ctrl_slave.gnt       ),
    .ctrl_pe_targ_r_valid_o  ( pe_ctrl_slave.r_valid   ),
    .ctrl_pe_targ_r_data_o   ( pe_ctrl_slave.r_rdata   ),
    .ctrl_pe_targ_r_opc_o    ( pe_ctrl_slave.r_opc     ),
    .ctrl_pe_targ_r_id_o     ( pe_ctrl_slave.r_id      ),
    .ctrl_targ_req_i         ( s_ctrl_bus_req          ),
    .ctrl_targ_type_i        ( s_ctrl_bus_wen          ),
    .ctrl_targ_be_i          ( s_ctrl_bus_be           ),
    .ctrl_targ_add_i         ( s_ctrl_bus_add          ),
    .ctrl_targ_data_i        ( s_ctrl_bus_wdata        ),
    .ctrl_targ_gnt_o         ( s_ctrl_bus_gnt          ),
    .ctrl_targ_r_valid_o     ( s_ctrl_bus_r_valid      ),
    .ctrl_targ_r_data_o      ( s_ctrl_bus_r_rdata      ),
    .dma_req_valid_i         ( ext_dma_req_valid_i     ),
    .dma_req_ready_o         ( ext_dma_req_ready_o     ),
    .dma_req_i               ( ext_dma_req_i           ),
    .dma_rsp_valid_o         ( ext_dma_rsp_valid_o     ),
    .axi_dma_req_o           ( axi_dma_req             ),
    .axi_dma_res_i           ( axi_dma_res             ),
    .busy_o                  ( busy_o                  ),
    .term_event_o            ( term_event_o            ),
    .term_irq_o              ( term_irq_o              ),
    .term_event_pe_o         ( term_event_pe_o         ),
    .term_irq_pe_o           ( term_irq_pe_o           ),
    .no_req_pending_o        ( no_req_pending_o        )
  );

  // xbar
  localparam int unsigned NumRules = 3;
  typedef axi_pkg::xbar_rule_32_t xbar_rule_t;
  axi_pkg::xbar_rule_32_t [NumRules-1:0] addr_map;
  logic [31:0] cluster_base_addr;
  assign cluster_base_addr = 64'h0000_0000_1000_0000 + (cluster_id_i << 22);
  // assign cluster_base_addr = 64'h0000_0000_1000_0000;
  assign addr_map = '{
    '{ // SoC low
      start_addr: 64'h0000_0000_0000_0000,
      end_addr:   cluster_base_addr,
      idx:        0
    },
    '{ // TCDM
      start_addr: cluster_base_addr,
      end_addr:   cluster_base_addr + 24'h10_0000,
      idx:        1
    },
    '{ // SoC high
      start_addr: cluster_base_addr + 24'h10_0000,
      end_addr:   64'hffff_ffff_ffff_ffff,
      idx:        0
    }
  };
  localparam NumMstPorts = 2;
  localparam NumSlvPorts = 1;

  /* verilator lint_off WIDTHCONCAT */
  localparam axi_pkg::xbar_cfg_t XbarCfg = '{
    NoSlvPorts:                    NumSlvPorts,
    NoMstPorts:                    NumMstPorts,
    MaxMstTrans:                            16,
    MaxSlvTrans:                            32,
    FallThrough:                          1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_PORTS,
    AxiIdWidthSlvPorts:       DMA_AXI_ID_WIDTH,
    AxiIdUsedSlvPorts:        DMA_AXI_ID_WIDTH,
    AxiAddrWidth:             DMA_AXI_AW_WIDTH,
    AxiDataWidth:             DMA_AXI_DW_WIDTH,
    NoAddrRules:                      NumRules
  };
  /* verilator lint_on WIDTHCONCAT */

  axi_xbar #(
    .Cfg          ( XbarCfg                 ),
    .slv_aw_chan_t( aw_chan_t               ),
    .mst_aw_chan_t( aw_chan_t               ),
    .w_chan_t     ( w_chan_t                ),
    .slv_b_chan_t ( b_chan_t                ),
    .mst_b_chan_t ( b_chan_t                ),
    .slv_ar_chan_t( ar_chan_t               ),
    .mst_ar_chan_t( ar_chan_t               ),
    .slv_r_chan_t ( r_chan_t                ),
    .mst_r_chan_t ( r_chan_t                ),
    .slv_req_t    ( axi_dma_req_t           ),
    .slv_resp_t   ( axi_dma_resp_t          ),
    .mst_req_t    ( axi_dma_req_t           ),
    .mst_resp_t   ( axi_dma_resp_t          ),
    .rule_t       ( axi_pkg::xbar_rule_32_t )
  ) i_wide_dma_axi_xbar (
    .clk_i                  ( clk_i                                    ),
    .rst_ni                 ( rst_ni                                   ),
    .test_i                 ( test_mode_i                              ),
    .slv_ports_req_i        ( axi_dma_req                              ),
    .slv_ports_resp_o       ( axi_dma_res                              ),
    .mst_ports_req_o        ( '{ axi_dma_tcdm_req, axi_dma_soc_req }   ),
    .mst_ports_resp_i       ( '{ axi_dma_tcdm_res, axi_dma_soc_res }   ),
    .addr_map_i             ( addr_map                                 ),
    .en_default_mst_port_i  ( '0                                       ),
    .default_mst_port_i     ( '0                                       )
  );

  // connect to external AXI
  `AXI_ASSIGN_FROM_REQ(s_wide_dma_soc, axi_dma_soc_req);
  `AXI_ASSIGN_TO_RESP (axi_dma_soc_res, s_wide_dma_soc);

  // the data returned by the memories is always valid 1 cycle later
  // this is usually handled by the TCDM interconnect correctly
  // we bypass TCDM ic here -> this delay needs to be explicitly
  // calculated.
  logic ext_dma_vld;
  always_ff @(posedge clk_i) begin : proc_delay_gnt_by_one
    if(~rst_ni) begin
      ext_dma_vld <= 0;
    end else begin
      ext_dma_vld <= s_wide_dma_superbanks.gnt & s_wide_dma_superbanks.req;
    end
  end

  axi_to_mem_interleaved #(
    .axi_req_t   ( axi_dma_req_t      ),
    .axi_resp_t  ( axi_dma_resp_t     ),
    .AddrWidth   ( DMA_AXI_AW_WIDTH   ),
    .DataWidth   ( DMA_AXI_DW_WIDTH   ),
    .IdWidth     ( DMA_AXI_ID_WIDTH   ),
    .NumBanks    ( 1                  ), // Needs to be 1
    .BufDepth    ( 4                  )  // TODO: tune me
  ) i_axi_to_mem (
    .clk_i        ( clk_i                           ),
    .rst_ni       ( rst_ni                          ),
    .busy_o       ( ),
    .axi_req_i    ( axi_dma_tcdm_req                ),
    .axi_resp_o   ( axi_dma_tcdm_res                ),
    .mem_req_o    ( s_wide_dma_superbanks.req       ),
    .mem_gnt_i    ( s_wide_dma_superbanks.gnt       ),
    .mem_addr_o   ( s_wide_dma_superbanks.add       ),
    .mem_wdata_o  ( s_wide_dma_superbanks.wdata     ),
    .mem_strb_o   ( s_wide_dma_superbanks.be        ),
    .mem_atop_o   ( ),
    .mem_we_o     ( s_wide_dma_superbanks.wen       ),
    .mem_rvalid_i ( ext_dma_vld                     ),
    .mem_rdata_i  ( s_wide_dma_superbanks.r_rdata   )
  );

  // tie-off unused pulp ports
  assign s_tcdm_bus_req                     = '0;
  assign s_tcdm_bus_add                     = '0;
  assign s_tcdm_bus_wen                     = '0;
  assign s_tcdm_bus_be                      = '0;
  assign s_tcdm_bus_wdata                   = '0;
  assign internal.aw_valid                  = '0;
  assign internal.aw_addr                   = '0;
  assign internal.aw_prot                   = '0;
  assign internal.aw_region                 = '0;
  assign internal.aw_atop                   = '0;
  assign internal.aw_len                    = '0;
  assign internal.aw_size                   = '0;
  assign internal.aw_burst                  = '0;
  assign internal.aw_lock                   = '0;
  assign internal.aw_cache                  = '0;
  assign internal.aw_qos                    = '0;
  assign internal.aw_id[AXI_ID_WIDTH-1:0]   = '0;
  assign internal.aw_user                   = '0;
  assign internal.ar_valid                  = '0;
  assign internal.ar_addr                   = '0;
  assign internal.ar_prot                   = '0;
  assign internal.ar_region                 = '0;
  assign internal.ar_len                    = '0;
  assign internal.ar_size                   = '0;
  assign internal.ar_burst                  = '0;
  assign internal.ar_lock                   = '0;
  assign internal.ar_cache                  = '0;
  assign internal.ar_qos                    = '0;
  assign internal.ar_id[AXI_ID_WIDTH-1:0]   = '0;
  assign internal.ar_user                   = '0;
  assign internal.w_valid                   = '0;
  assign internal.w_data                    = '0;
  assign internal.w_strb                    = '0;
  assign internal.w_user                    = '0;
  assign internal.r_ready                   = '0;
  assign internal.b_ready                   = '0;

endmodule
