// Copyright (c) 2021 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "axi/assign.svh"
`include "axi/typedef.svh"
`include "common_cells/assertions.svh"

module pspin 
  import pspin_cfg_pkg::*;
#(
  // AXI interfaces
  parameter type                          host_in_req_t     = logic,
  parameter type                          host_in_resp_t    = logic,
  parameter type                          host_out_req_t    = logic,
  parameter type                          host_out_resp_t   = logic,
  parameter type                          ni_in_req_t       = logic,
  parameter type                          ni_in_resp_t      = logic,
  parameter type                          no_in_req_t       = logic,
  parameter type                          no_in_resp_t      = logic
) (
  // Clocks and Resets
  input  logic                            clk_i,
  input  logic                            rst_ni,

  // Host interface
  input  host_in_req_t                    host_wide_req_i,
  output host_in_resp_t                   host_wide_resp_o,
  output host_out_req_t                   host_wide_req_o,
  input  host_out_resp_t                  host_wide_resp_i,
  
  // From NIC inbound
  output logic                            her_ready_o,
  input  logic                            her_valid_i,
  input  her_descr_t                      her_i,
  input  ni_in_req_t                      ni_wide_req_i,
  output ni_in_resp_t                     ni_wide_resp_o,

  // To NIC inbound
  input  logic                            nic_feedback_ready_i,
  output logic                            nic_feedback_valid_o,
  output feedback_descr_t                 nic_feedback_o,

  // To NIC command unit
  input  logic                            nic_cmd_ready_i,
  output logic                            nic_cmd_valid_o,
  output pspin_cmd_req_t                  nic_cmd_o,

  // From NIC command unit
  input  logic                            nic_cmd_resp_valid_i,
  input  pspin_cmd_resp_t                 nic_cmd_resp_i,

  // From NIC outbound 
  input  no_in_req_t                      no_wide_req_i,
  output no_in_resp_t                     no_wide_resp_o,

  // Termination signal (used for simulations)
  input  logic                            eos_i,

  // Asserted once HPUs are ready                   
  output logic                            pspin_active_o
);

  //********************//
  // Cluster interfaces //
  //********************//

  // Narrow channels (load/store)
  snitch_cluster_cfg_pkg::narrow_out_req_t    [NUM_CLUSTERS-1:0]  cl_narrow_out_req;
  snitch_cluster_cfg_pkg::narrow_out_resp_t   [NUM_CLUSTERS-1:0]  cl_narrow_out_resp;

  snitch_cluster_cfg_pkg::narrow_in_req_t     [NUM_CLUSTERS-1:0]  cl_narrow_in_req;
  snitch_cluster_cfg_pkg::narrow_in_resp_t    [NUM_CLUSTERS-1:0]  cl_narrow_in_resp;

  // Wide channels (DMA)
  snitch_cluster_cfg_pkg::wide_out_req_t      [NUM_CLUSTERS-1:0]  cl_wide_out_req;
  snitch_cluster_cfg_pkg::wide_out_resp_t     [NUM_CLUSTERS-1:0]  cl_wide_out_resp;

  snitch_cluster_cfg_pkg::wide_in_req_t       [NUM_CLUSTERS-1:0]  cl_wide_in_req;
  snitch_cluster_cfg_pkg::wide_in_resp_t      [NUM_CLUSTERS-1:0]  cl_wide_in_resp;

  //***************//
  // L2 interfaces //
  //***************//

  soc_wide_req_t   pe_l2d_req,  dma_l2_req,   l2_hnd_req_a,  l2_hnd_req_b,  l2_pkt_req_a,  l2_pkt_req_b;
  soc_wide_resp_t  pe_l2d_resp, dma_l2_resp,  l2_hnd_resp_a, l2_hnd_resp_b, l2_pkt_resp_a, l2_pkt_resp_b;
  
  soc_narrow_req_t  pe_l2i_req;
  soc_narrow_resp_t pe_l2i_resp;

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_SOC_AW),
    .AXI_DATA_WIDTH (AXI_WIDE_DW),
    .AXI_ID_WIDTH   (AXI_IW),
    .AXI_USER_WIDTH (AXI_UW)
  ) l2_hnd_mst_a(), l2_pkt_mst_a(), l2_hnd_mst_b(), l2_pkt_mst_b();

  `AXI_ASSIGN_FROM_REQ(l2_hnd_mst_a, l2_hnd_req_a)
  `AXI_ASSIGN_TO_RESP(l2_hnd_resp_a, l2_hnd_mst_a)
  
  `AXI_ASSIGN_FROM_REQ(l2_hnd_mst_b, l2_hnd_req_b)
  `AXI_ASSIGN_TO_RESP(l2_hnd_resp_b, l2_hnd_mst_b)

  `AXI_ASSIGN_FROM_REQ(l2_pkt_mst_a, l2_pkt_req_a)
  `AXI_ASSIGN_TO_RESP(l2_pkt_resp_a, l2_pkt_mst_a)

  `AXI_ASSIGN_FROM_REQ(l2_pkt_mst_b, l2_pkt_req_b)
  `AXI_ASSIGN_TO_RESP(l2_pkt_resp_b, l2_pkt_mst_b)

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_SOC_AW),
    .AXI_DATA_WIDTH (AXI_WIDE_DW),
    .AXI_ID_WIDTH   (AXI_IW),
    .AXI_USER_WIDTH (AXI_UW)
  ) l2_hnd_mst_wo_atomics();

  //****************//
  // Internal wires //
  //****************//

  // eDMA -> NHI
  soc_wide_req_t                                    nhi_mst_edma_req;
  soc_wide_resp_t                                   nhi_mst_edma_resp;
 
  // mpq_engine -> scheduler
  logic                                             mpqengine_scheduler_valid;
  logic                                             mpqengine_scheduler_ready;
  handler_task_t                                    mpqengine_scheduler_task;

  // scheduler -> mpq_engine
  logic                                             scheduler_mpqengine_valid;
  logic                                             scheduler_mpqengine_ready;
  feedback_descr_t                                  scheduler_mpqengine_feedback;

  // scheduler -> cluster_schedulers
  logic [NUM_CLUSTERS-1:0]                          sched_loc_valid;
  logic [NUM_CLUSTERS-1:0]                          sched_loc_ready;
  handler_task_t [NUM_CLUSTERS-1:0]                 sched_loc_task;

  // cluster_schedulers -> scheduler 
  logic [NUM_CLUSTERS-1:0]                          loc_sched_valid;
  logic [NUM_CLUSTERS-1:0]                          loc_sched_ready;
  feedback_descr_t [NUM_CLUSTERS-1:0]               loc_sched_feedback;

  // clusters -> command unit
  logic [NUM_CLUSTERS-1:0]                          cluster_cmd_ready;
  logic [NUM_CLUSTERS-1:0]                          cluster_cmd_valid;
  pspin_cmd_req_t [NUM_CLUSTERS-1:0]                cluster_cmd;
  pspin_cmd_intf_id_t [NUM_CLUSTERS-1:0]            cluster_cmd_intf_selector;

  // command unit -> clusters
  logic                                             cluster_cmd_resp_valid;
  pspin_cmd_resp_t                                  cluster_cmd_resp;

  // CMD unit <-> soc-level DMA
  logic                                             edma_cmd_ready;
  logic                                             edma_cmd_valid;
  pspin_cmd_req_t                                   edma_cmd;
  logic                                             edma_resp_valid;
  pspin_cmd_resp_t                                  edma_resp;

  // CMD unit <-> HostDirect unit
  logic                                             hdir_cmd_valid;
  logic                                             hdir_cmd_ready;
  pspin_cmd_req_t                                   hdir_cmd;
  logic                                             hdir_resp_valid;
  pspin_cmd_resp_t                                  hdir_resp;
  
  // "Active" clusters signal
  logic [NUM_CLUSTERS-1:0]                          cluster_active;

  // HOST -> NHI -> L2_PROG -> L2_PROG_NARROW
  soc_wide_req_t                                    host_l2_prog_req;
  soc_wide_resp_t                                   host_l2_prog_resp;
  soc_narrow_req_t                                  host_slv_downsized_req;
  soc_narrow_resp_t                                 host_slv_downsized_resp;

  // {DMA, HOST_DIRECT} -> HOST
  host_wide_req_t                                   host_mst_soc_dma_req, host_mst_hdir_req;
  host_wide_resp_t                                  host_mst_soc_dma_resp, host_mst_hdir_resp;

  // NHI -> CLUSTERS (to cluster_noc for demultiplixeing)
  soc_wide_req_t                                    nhi_req;
  soc_wide_resp_t                                   nhi_resp;

  //***************//
  // Active signal //
  //***************//

  assign pspin_active_o = (~cluster_active == '0);

  //*************//
  // Address map //
  //*************//

  // Clusters addresses
  addr_t [NUM_CLUSTERS-1:0] cl_start_addr, cl_end_addr;
  for (genvar i = 0; i < NUM_CLUSTERS; i++) begin : gen_map_clusters
      assign cl_start_addr[i] = L1_CLUSTER_BASE +  i    * L1_CLUSTER_SPAN;
      assign cl_end_addr[i]   = L1_CLUSTER_BASE + (i+1) * L1_CLUSTER_SPAN - 1;
  end

  //*******************//
  // L2 program memory //
  //*******************//

  // TODO: remove mux in prog_mem. 
  prog_mem #(
    .NumClusters  (1),
    .NumBytes     (L2_PROG_SIZE),
    .AddrWidth    (AXI_SOC_AW),
    .DataWidth    (AXI_NARROW_DW),
    .IdWidth      (AXI_IW),
    .UserWidth    (AXI_UW),
    .req_t        (soc_narrow_req_t),
    .resp_t       (soc_narrow_resp_t)
  ) i_prog_mem (
    .clk_i        ( clk_i                   ),
    .rst_ni       ( rst_ni                  ),
    .cl_req_i     ( pe_l2i_req              ),
    .cl_resp_o    ( pe_l2i_resp             ),
    .host_req_i   ( host_slv_downsized_req  ),
    .host_resp_o  ( host_slv_downsized_resp )
  );

  axi_dw_downsizer #(
    .AxiMaxReads         ( 4                    ), // Number of outstanding reads
    .AxiSlvPortDataWidth ( AXI_WIDE_DW          ), // Data width of the slv port
    .AxiMstPortDataWidth ( AXI_NARROW_DW        ), // Data width of the mst port
    .AxiAddrWidth        ( AXI_SOC_AW           ), // Address width
    .AxiIdWidth          ( AXI_IW               ), // ID width
    .aw_chan_t           ( soc_narrow_aw_chan_t ), // AW Channel Type
    .mst_w_chan_t        ( soc_narrow_w_chan_t  ), //  W Channel Type for the mst port
    .slv_w_chan_t        ( host_wide_w_chan_t   ), //  W Channel Type for the slv port
    .b_chan_t            ( soc_narrow_b_chan_t  ), //  B Channel Type
    .ar_chan_t           ( soc_narrow_ar_chan_t ), // AR Channel Type
    .mst_r_chan_t        ( soc_narrow_r_chan_t  ), //  R Channel Type for the mst port
    .slv_r_chan_t        ( host_wide_r_chan_t   ), //  R Channel Type for the slv port
    .axi_mst_req_t       ( soc_narrow_req_t     ), // AXI Request Type for mst ports
    .axi_mst_resp_t      ( soc_narrow_resp_t    ), // AXI Response Type for mst ports
    .axi_slv_req_t       ( soc_wide_req_t       ), // AXI Request Type for slv ports
    .axi_slv_resp_t      ( soc_wide_resp_t      )  // AXI Response Type for slv ports
  ) i_dw_downsizer_host_l2_prog (
    .clk_i               ( clk_i                   ),
    .rst_ni              ( rst_ni                  ),
    .slv_req_i           ( host_l2_prog_req        ),
    .slv_resp_o          ( host_l2_prog_resp       ), 
    .mst_req_o           ( host_slv_downsized_req  ),
    .mst_resp_i          ( host_slv_downsized_resp )
  );

  //*******************//
  // L2 handler memory //
  //*******************//

  l2_mem #(
    .AXI_AW         (AXI_SOC_AW),
    .AXI_DW         (AXI_WIDE_DW),
    .AXI_UW         (AXI_UW),
    .AXI_IW         (AXI_IW),
    .N_BYTES        (L2_HND_SIZE),
    .CUT_DW         (L2_HND_CUT_DW),
    .CUT_N_WORDS    (L2_HND_CUT_N_WORDS),
    .N_PAR_CUTS     (L2_HND_N_PAR_CUTS)
  ) i_l2_hnd_mem (
    .clk_i          ( clk_i                 ),
    .rst_ni         ( rst_ni                ),
    .slv_a          ( l2_hnd_mst_wo_atomics ),
    .slv_b          ( l2_hnd_mst_b          )
  );

  axi_riscv_atomics_wrap #(
    .AXI_ADDR_WIDTH     (AXI_SOC_AW),
    .AXI_DATA_WIDTH     (AXI_WIDE_DW),
    .AXI_ID_WIDTH       (AXI_IW),
    .AXI_USER_WIDTH     (AXI_UW),
    .AXI_MAX_WRITE_TXNS (4),
    .RISCV_WORD_WIDTH   (32)
  ) i_atomics (
    .clk_i              ( clk_i                 ),
    .rst_ni             ( rst_ni                ),
    .slv                ( l2_hnd_mst_a          ),
    .mst                ( l2_hnd_mst_wo_atomics )
  );

  //******************//
  // L2 packet memory //
  //******************//
  
  l2_mem #(
    .AXI_AW         (AXI_SOC_AW),
    .AXI_DW         (AXI_WIDE_DW),
    .AXI_UW         (AXI_UW),
    .AXI_IW         (AXI_IW),
    .N_BYTES        (L2_PKT_SIZE),
    .CUT_DW         (L2_PKT_CUT_DW),
    .CUT_N_WORDS    (L2_PKT_CUT_N_WORDS),
    .N_PAR_CUTS     (L2_PKT_N_PAR_CUTS)
  ) i_l2_pkt_mem (
    .clk_i,
    .rst_ni,
    .slv_a    (l2_pkt_mst_a),
    .slv_b    (l2_pkt_mst_b)
  );
  
  //**************************//
  // Inter-cluster scheduling //
  //**************************//
  
  mpq_engine #(
    .NUM_HER_SLOTS          (NUM_MPQ_CELLS),
    .NUM_MPQ                (NUM_MPQ) 
  ) i_mpq_engine (
    .rst_ni                 (rst_ni),
    .clk_i                  (clk_i),

    .her_ready_o            (her_ready_o),
    .her_valid_i            (her_valid_i),
    .her_i                  (her_i),

    .eos_i                  (eos_i),

    .mpq_full_o             (),

    .nic_feedback_ready_i   (nic_feedback_ready_i),
    .nic_feedback_valid_o   (nic_feedback_valid_o),
    .nic_feedback_o         (nic_feedback_o),

    .feedback_ready_o       (scheduler_mpqengine_ready),
    .feedback_valid_i       (scheduler_mpqengine_valid),
    .feedback_i             (scheduler_mpqengine_feedback),

    .task_ready_i           (mpqengine_scheduler_ready),
    .task_valid_o           (mpqengine_scheduler_valid),
    .task_o                 (mpqengine_scheduler_task)

  );

  scheduler #(
    .NUM_CLUSTERS             (NUM_CLUSTERS),
    .NUM_HERS_PER_CLUSTER     (NUM_HERS_PER_CLUSTER)
  ) i_scheduler (
    .rst_ni                   (rst_ni),
    .clk_i                    (clk_i),

    //from MPQ engine
    .task_valid_i             (mpqengine_scheduler_valid),
    .task_ready_o             (mpqengine_scheduler_ready),
    .task_descr_i             (mpqengine_scheduler_task),

    // to MPQ engine
    .feedback_valid_o         (scheduler_mpqengine_valid),
    .feedback_ready_i         (scheduler_mpqengine_ready),
    .feedback_o               (scheduler_mpqengine_feedback),

    // to cluster_schedulers
    .cluster_task_valid_o     (sched_loc_valid),
    .cluster_task_ready_i     (sched_loc_ready),
    .cluster_task_descr_o     (sched_loc_task),

    // from cluster schedulers
    .cluster_feedback_valid_i (loc_sched_valid),
    .cluster_feedback_ready_o (loc_sched_ready),
    .cluster_feedback_i       (loc_sched_feedback)
  );
  
  //************************************//
  // Command unit (dispatches commands) //
  //************************************//
  
  for (genvar i = 0; i < NUM_CLUSTERS; i++) begin : gen_cmds_selector
    assign cluster_cmd_intf_selector[i] = cluster_cmd[i].intf_id;
  end

  cmd_xbar #(
    .CUT_SLV_PORTS               (1'b1),
    .NUM_SLV_PORTS               (NUM_CLUSTERS),
    .NUM_MST_PORTS               (NUM_SOC_CMD_INTERFACES),
    .cmd_req_t                   (pspin_cmd_req_t),
    .cmd_resp_t                  (pspin_cmd_resp_t)
  ) i_cmd_xbar (
    .rst_ni                      (rst_ni),
    .clk_i                       (clk_i),

    //commands from clusters
    .cmd_ready_o                 (cluster_cmd_ready),
    .cmd_valid_i                 (cluster_cmd_valid),
    .cmd_i                       (cluster_cmd),
    .cmd_intf_selector_i         (cluster_cmd_intf_selector),

    //command responses to clusters
    .cmd_resp_valid_o            (cluster_cmd_resp_valid),
    .cmd_resp_o                  (cluster_cmd_resp),

    //command interfaces requests
    .intf_ready_i                ({edma_cmd_ready,  nic_cmd_ready_i, hdir_cmd_ready}),
    .intf_valid_o                ({edma_cmd_valid,  nic_cmd_valid_o, hdir_cmd_valid}),
    .intf_cmd_o                  ({edma_cmd,        nic_cmd_o,       hdir_cmd}),

    //command interfaces responses
    .intf_cmd_resp_valid_i       ({edma_resp_valid, nic_cmd_resp_valid_i, hdir_resp_valid}),
    .intf_cmd_resp_i             ({edma_resp,       nic_cmd_resp_i,       hdir_resp})
  );
  
  //**********************************************************//
  // SOC DMA engine (receives commands from the command unit) //
  //**********************************************************//
  
  soc_dma_wrap #(
    .DmaAxiIdWidth     (AXI_IW),
    .DmaDataWidth      (AXI_WIDE_DW),
    .DmaUserWidth      (AXI_UW),
    .AxiAxReqDepth     (SOC_DMA_AXI_REQ_DEPTH),
    .TfReqFifoDepth    (SOC_DMA_REQ_FIFO_DEPT),
    .axi_nhi_req_t     (soc_wide_req_t),
    .axi_nhi_res_t     (soc_wide_resp_t),
    .axi_host_req_t    (host_wide_req_t),
    .axi_host_res_t    (host_wide_resp_t)
  ) i_soc_dma_wrap (
    .clk_i             (clk_i),
    .rst_ni            (rst_ni),

    .cmd_req_valid_i   (edma_cmd_valid),
    .cmd_req_ready_o   (edma_cmd_ready),
    .cmd_req_i         (edma_cmd),
    
    .cmd_resp_valid_o  (edma_resp_valid),
    .cmd_resp_o        (edma_resp),

    //AXI wide port 1 (to NHI)
    .nhi_req_o         (nhi_mst_edma_req),
    .nhi_resp_i        (nhi_mst_edma_resp),
    //AXI wide port 2 (to HOST)
    .host_req_o        (host_mst_soc_dma_req),
    .host_resp_i       (host_mst_soc_dma_resp)
  );
  
  //**********************************************************//
  // Host direct    (receives commands from the command unit) //
  //**********************************************************//
  
  host_direct #(
    .AXI_AW             (AXI_HOST_AW),
    .AXI_DW             (AXI_WIDE_DW),
    .CMD_IMM_DATA_SIZE  (AXI_WIDE_DW),
    .axi_host_aw_t      (host_wide_aw_chan_t),
    .axi_host_ar_t      (host_wide_ar_chan_t),
    .axi_host_w_t       (host_wide_w_chan_t),
    .axi_host_r_t       (host_wide_r_chan_t),
    .axi_host_b_t       (host_wide_b_chan_t),
    .axi_host_req_t     (host_wide_req_t),
    .axi_host_res_t     (host_wide_resp_t),
    .cmd_req_t          (pspin_cmd_req_t),
    .cmd_res_t          (pspin_cmd_resp_t),
    .cmd_id_t           (pspin_cmd_id_t)
  ) i_host_direct (
    .clk_i              (clk_i),
    .rst_ni             (rst_ni),

    .cmd_req_valid_i    (hdir_cmd_valid),
    .cmd_req_ready_o    (hdir_cmd_ready),
    .cmd_req_i          (hdir_cmd),

    .cmd_resp_valid_o   (hdir_resp_valid),
    .cmd_resp_o         (hdir_resp),

    .host_req_o         (host_mst_hdir_req),
    .host_resp_i        (host_mst_hdir_resp)
  );
  
  //**********//
  // Clusters //
  //**********//

  for (genvar i = 0; i < NUM_CLUSTERS; i++) begin: gen_clusters
    logic [31:0] hart_base_id;
    logic [snitch_cluster_cfg_pkg::PhysicalAddrWidth-1:0] l1_pkt_buff_base_addr;

    //assign hart_base_id = i * (snitch_cluster_cfg_pkg::NrCores);
    assign hart_base_id[31:16] = i;
    assign hart_base_id[15:0] = '0;
    assign l1_pkt_buff_base_addr = cl_start_addr[i] + L1_PKT_BUFF_OFFSET;

    snitch_cluster #(
      .PhysicalAddrWidth (snitch_cluster_cfg_pkg::PhysicalAddrWidth),
      .NarrowDataWidth (snitch_cluster_cfg_pkg::NarrowDataWidth),
      .WideDataWidth (snitch_cluster_cfg_pkg::WideDataWidth),
      .NarrowIdWidthIn (snitch_cluster_cfg_pkg::NarrowIdWidthIn),
      .WideIdWidthIn (snitch_cluster_cfg_pkg::WideIdWidthIn),
      .UserWidth (snitch_cluster_cfg_pkg::UserWidth),
      .BootAddr (snitch_cluster_cfg_pkg::BootAddr),
      .narrow_in_req_t (snitch_cluster_cfg_pkg::narrow_in_req_t),
      .narrow_in_resp_t (snitch_cluster_cfg_pkg::narrow_in_resp_t),
      .narrow_out_req_t (snitch_cluster_cfg_pkg::narrow_out_req_t),
      .narrow_out_resp_t (snitch_cluster_cfg_pkg::narrow_out_resp_t),
      .wide_out_req_t (snitch_cluster_cfg_pkg::wide_out_req_t),
      .wide_out_resp_t (snitch_cluster_cfg_pkg::wide_out_resp_t),
      .wide_in_req_t (snitch_cluster_cfg_pkg::wide_in_req_t),
      .wide_in_resp_t (snitch_cluster_cfg_pkg::wide_in_resp_t),
      .NrHives (snitch_cluster_cfg_pkg::NrHives),
      .NrCores (snitch_cluster_cfg_pkg::NrCores),
      .TCDMDepth (snitch_cluster_cfg_pkg::TCDMDepth),
      .NrBanks (snitch_cluster_cfg_pkg::TCDMBanks),
      .DMAAxiReqFifoDepth (snitch_cluster_cfg_pkg::DMAAxiReqFifoDepth),
      .DMAReqFifoDepth (snitch_cluster_cfg_pkg::DMAReqFifoDepth),
      .ICacheLineWidth (snitch_cluster_cfg_pkg::ICacheLineWidth),
      .ICacheLineCount (snitch_cluster_cfg_pkg::ICacheLineCount),
      .ICacheSets (snitch_cluster_cfg_pkg::ICacheSets),
      .RVE (snitch_cluster_cfg_pkg::RVE),
      .RVF (snitch_cluster_cfg_pkg::RVF),
      .RVD (snitch_cluster_cfg_pkg::RVD),
      .XF16 (snitch_cluster_cfg_pkg::XF16),
      .XF16ALT (snitch_cluster_cfg_pkg::XF16ALT),
      .XF8 (snitch_cluster_cfg_pkg::XF8),
      .XFVEC (snitch_cluster_cfg_pkg::XFVEC),
      .Xdma (snitch_cluster_cfg_pkg::Xdma),
      .Xssr (snitch_cluster_cfg_pkg::Xssr),
      .Xfrep (snitch_cluster_cfg_pkg::Xfrep),
      .FPUImplementation (snitch_cluster_cfg_pkg::FPUImplementation),
      .SnitchPMACfg (snitch_cluster_cfg_pkg::SnitchPMACfg),
      .NumIntOutstandingLoads (snitch_cluster_cfg_pkg::NumIntOutstandingLoads),
      .NumIntOutstandingMem (snitch_cluster_cfg_pkg::NumIntOutstandingMem),
      .NumFPOutstandingLoads (snitch_cluster_cfg_pkg::NumFPOutstandingLoads),
      .NumFPOutstandingMem (snitch_cluster_cfg_pkg::NumFPOutstandingMem),
      .NumDTLBEntries (snitch_cluster_cfg_pkg::NumDTLBEntries),
      .NumITLBEntries (snitch_cluster_cfg_pkg::NumITLBEntries),
      .NumSsrsMax (snitch_cluster_cfg_pkg::NumSsrsMax),
      .NumSsrs (snitch_cluster_cfg_pkg::NumSsrs),
      .SsrMuxRespDepth (snitch_cluster_cfg_pkg::SsrMuxRespDepth),
      .SsrRegs (snitch_cluster_cfg_pkg::SsrRegs),
      .SsrCfgs (snitch_cluster_cfg_pkg::SsrCfgs),
      .NumSequencerInstr (snitch_cluster_cfg_pkg::NumSequencerInstr),
      .Hive (snitch_cluster_cfg_pkg::Hive),
      .Topology (snitch_pkg::LogarithmicInterconnect),
      .Radix (snitch_cluster_cfg_pkg::Radix),
      .RegisterOffloadReq (snitch_cluster_cfg_pkg::RegisterOffloadReq),
      .RegisterOffloadRsp (snitch_cluster_cfg_pkg::RegisterOffloadRsp),
      .RegisterCoreReq (snitch_cluster_cfg_pkg::RegisterCoreReq),
      .RegisterCoreRsp (snitch_cluster_cfg_pkg::RegisterCoreRsp),
      .RegisterTCDMCuts (snitch_cluster_cfg_pkg::RegisterTCDMCuts),
      .RegisterExtWide (snitch_cluster_cfg_pkg::RegisterExtWide),
      .RegisterExtNarrow (snitch_cluster_cfg_pkg::RegisterExtNarrow),
      .RegisterFPUReq (snitch_cluster_cfg_pkg::RegisterFPUReq),
      .RegisterSequencer (snitch_cluster_cfg_pkg::RegisterSequencer),
      .IsoCrossing (snitch_cluster_cfg_pkg::IsoCrossing),
      .NarrowXbarLatency (axi_pkg::CUT_ALL_PORTS),
      .WideXbarLatency (axi_pkg::CUT_ALL_PORTS),
      .HERCount (pspin_cfg_pkg::NUM_HERS_PER_CLUSTER),
      .L1PktBuffSize (pspin_cfg_pkg::L1_PKT_BUFF_SIZE),
      .NumCmds (pspin_cfg_pkg::NUM_HPU_CMDS),
      .ClusterIdWidth (pspin_cfg_pkg::CLUSTER_ID_WIDTH),
      .CoreIdWidth (pspin_cfg_pkg::HART_ID_WIDTH),
      .HPUDriverMemSize (pspin_cfg_pkg::HPU_DRIVER_SIZE),
      .handler_task_t (pspin_cfg_pkg::handler_task_t),
      .hpu_handler_task_t (pspin_cfg_pkg::hpu_handler_task_t),
      .task_feedback_descr_t (pspin_cfg_pkg::task_feedback_descr_t),
      .feedback_descr_t (pspin_cfg_pkg::feedback_descr_t),
      .cmd_req_t (pspin_cfg_pkg::pspin_cmd_req_t),
      .cmd_resp_t (pspin_cfg_pkg::pspin_cmd_resp_t)
    ) i_cluster (
      .clk_i                  ( clk_i                     ),
      .rst_ni                 ( rst_ni                    ),
      .debug_req_i            ( '0                        ),
      .meip_i                 ( '0                        ),
      .mtip_i                 ( '0                        ),
      .msip_i                 ( '0                        ),
      .hart_base_id_i         ( hart_base_id              ),
      .cluster_base_addr_i    ( cl_start_addr[i]          ),
      .clk_d2_bypass_i        ( 1'b0                      ),
      .narrow_in_req_i        ( cl_narrow_in_req[i]       ),
      .narrow_in_resp_o       ( cl_narrow_in_resp[i]      ),
      .narrow_out_req_o       ( cl_narrow_out_req[i]      ),
      .narrow_out_resp_i      ( cl_narrow_out_resp[i]     ),
      .wide_out_req_o         ( cl_wide_out_req[i]        ),
      .wide_out_resp_i        ( cl_wide_out_resp[i]       ),
      .wide_in_req_i          ( cl_wide_in_req[i]         ),
      .wide_in_resp_o         ( cl_wide_in_resp[i]        ),
      .task_valid_i           ( sched_loc_valid[i]        ),
      .task_ready_o           ( sched_loc_ready[i]        ),
      .task_descr_i           ( sched_loc_task[i]         ),
      .feedback_valid_o       ( loc_sched_valid[i]        ),
      .feedback_ready_i       ( loc_sched_ready[i]        ),
      .feedback_o             ( loc_sched_feedback[i]     ),
      .cluster_active_o       ( cluster_active[i]         ),
      .cmd_ready_i            ( cluster_cmd_ready[i]      ),
      .cmd_valid_o            ( cluster_cmd_valid[i]      ),
      .cmd_o                  ( cluster_cmd[i]            ),
      .cmd_resp_valid_i       ( cluster_cmd_resp_valid    ),
      .cmd_resp_i             ( cluster_cmd_resp          ),
      .hpu_driver_base_addr_i ( HPU_DRIVER_BASE_ADDR      ),
      .pkt_buff_start_addr_i  ( l1_pkt_buff_base_addr     )
    );
  end

  //*******************//
  // SOC interconnects //
  //*******************//

  // Muxes host-direct and DMA requests to host
  host_mst_mux #(
    .AddrWidth          (AXI_HOST_AW),
    .DataWidth          (AXI_WIDE_DW),
    .IdWidth            (AXI_IW),
    .UserWidth          (AXI_UW),
    .req_t              (host_wide_req_t),
    .resp_t             (host_wide_resp_t)
  ) i_mux_host_mst (
    .clk_i              (clk_i),
    .rst_ni             (rst_ni),
    .dma_req_i          (host_mst_soc_dma_req),
    .dma_resp_o         (host_mst_soc_dma_resp),
    .hdir_req_i         (host_mst_hdir_req),
    .hdir_resp_o        (host_mst_hdir_resp),
    .host_req_o         (host_wide_req_o),
    .host_resp_i        (host_wide_resp_i)
  );

  // Narrow accesses from HPUs to other clusters and L2
  pe_noc #(
    .NumClusters          (NUM_CLUSTERS),
    .AddrWidth            (AXI_SOC_AW),
    .ClDataWidth          (AXI_NARROW_DW),
    .ClOupIdWidth         (snitch_cluster_cfg_pkg::NarrowIdWidthOut),
    .ClInpIdWidth         (snitch_cluster_cfg_pkg::NarrowIdWidthIn),
    .L2DataDataWidth      (AXI_WIDE_DW),
    .L2ProgDataWidth      (AXI_NARROW_DW),
    .L2DataIdWidth        (AXI_IW),
    .L2ProgIdWidth        (AXI_IW),
    .UserWidth            (AXI_UW),
    .cl_oup_req_t         (snitch_cluster_cfg_pkg::narrow_out_req_t),
    .cl_oup_resp_t        (snitch_cluster_cfg_pkg::narrow_out_resp_t),
    .cl_inp_req_t         (snitch_cluster_cfg_pkg::narrow_in_req_t),
    .cl_inp_resp_t        (snitch_cluster_cfg_pkg::narrow_in_resp_t),
    .l2d_req_t            (soc_wide_req_t), 
    .l2d_resp_t           (soc_wide_resp_t),
    .l2i_req_t            (soc_narrow_req_t),
    .l2i_resp_t           (soc_narrow_resp_t)
  ) i_pe_noc (
    .clk_i                ( clk_i                              ),
    .rst_ni               ( rst_ni                             ),
    .cl_start_addr_i      ( cl_start_addr                      ),
    .cl_end_addr_i        ( cl_end_addr                        ),
    .l2d_start_addr_i     ( L2D_MIN_ADDR[AXI_SOC_AW-1:0]       ),
    .l2d_end_addr_i       ( L2D_MAX_ADDR[AXI_SOC_AW-1:0]       ),
    .l2i_start_addr_i     ( L2_PROG_ADDR_START[AXI_SOC_AW-1:0] ),
    .l2i_end_addr_i       ( L2_PROG_ADDR_END[AXI_SOC_AW-1:0]   ),
    .from_cl_req_i        ( cl_narrow_out_req                  ),
    .from_cl_resp_o       ( cl_narrow_out_resp                 ),
    .to_cl_req_o          ( cl_narrow_in_req                   ),
    .to_cl_resp_i         ( cl_narrow_in_resp                  ),
    .l2d_req_o            ( pe_l2d_req                         ),
    .l2d_resp_i           ( pe_l2d_resp                        ),
    .l2i_req_o            ( pe_l2i_req                         ),
    .l2i_resp_i           ( pe_l2i_resp                        )
  );

  // Wide accesses from cluster-local DMA engines to L2
  dma_noc #(
    .NumClusters          (NUM_CLUSTERS),
    .AddrWidth            (AXI_SOC_AW),
    .DataWidth            (AXI_WIDE_DW),
    .DMAIdWidth           (snitch_cluster_cfg_pkg::WideIdWidthOut),
    .L2IdWidth            (AXI_IW),
    .UserWidth            (AXI_UW),
    .dma_req_t            (snitch_cluster_cfg_pkg::wide_out_req_t),
    .dma_resp_t           (snitch_cluster_cfg_pkg::wide_out_resp_t),
    .l2_req_t             (soc_wide_req_t),
    .l2_resp_t            (soc_wide_resp_t)
  ) i_dma_noc (
    .clk_i                ( clk_i                        ),
    .rst_ni               ( rst_ni                       ),
    .l2_start_addr_i      ( L2D_MIN_ADDR[AXI_SOC_AW-1:0] ),
    .l2_end_addr_i        ( L2D_MAX_ADDR[AXI_SOC_AW-1:0] ),
    .dma_req_i            ( cl_wide_out_req              ),
    .dma_resp_o           ( cl_wide_out_resp             ),
    .l2_req_o             ( dma_l2_req                   ),
    .l2_resp_i            ( dma_l2_resp                  )
  );
  
  // Wide accesses from NHI slave ports to clusters
  cluster_noc #(
    .NumClusters  (NUM_CLUSTERS),
    .AddrWidth    (AXI_SOC_AW),
    .DataWidth    (AXI_WIDE_DW),
    .UserWidth    (AXI_UW),
    .NHIIdWidth   (AXI_IW),
    .ClIdWidth    (snitch_cluster_cfg_pkg::WideIdWidthIn),
    .nhi_req_t    (soc_wide_req_t),
    .nhi_resp_t   (soc_wide_resp_t),
    .cl_req_t     (snitch_cluster_cfg_pkg::wide_in_req_t),
    .cl_resp_t    (snitch_cluster_cfg_pkg::wide_in_resp_t)
  ) i_cluster_noc (
    .clk_i                ( clk_i             ),
    .rst_ni               ( rst_ni            ),
    .cl_start_addr_i      ( cl_start_addr     ),
    .cl_end_addr_i        ( cl_end_addr       ),
    .cl_req_o             ( cl_wide_in_req    ),
    .cl_resp_i            ( cl_wide_in_resp   ),
    .nhi_req_i            ( nhi_req           ),
    .nhi_resp_o           ( nhi_resp          )
  );

  // NHI crossbar
  nhi_xbar #(
    .AddrWidth  (AXI_SOC_AW),
    .DataWidth  (AXI_WIDE_DW),
    .IdWidth    (AXI_IW),
    .UserWidth  (AXI_UW),
    .req_t      (soc_wide_req_t),
    .resp_t     (soc_wide_resp_t)
  ) i_nhi_xbar (
    .clk_i,
    .rst_ni,
    .l2_hnd_start_addr_i  ( L2_HND_ADDR_START[AXI_SOC_AW-1:0]  ),
    .l2_hnd_end_addr_i    ( L2_HND_ADDR_END[AXI_SOC_AW-1:0]    ),
    .l2_pkt_start_addr_i  ( L2_PKT_ADDR_START[AXI_SOC_AW-1:0]  ),
    .l2_pkt_end_addr_i    ( L2_PKT_ADDR_END[AXI_SOC_AW-1:0]    ),
    .l2_prog_start_addr_i ( L2_PROG_ADDR_START[AXI_SOC_AW-1:0] ),
    .l2_prog_end_addr_i   ( L2_PROG_ADDR_END[AXI_SOC_AW-1:0]   ),
    .l1_start_addr_i      ( cl_start_addr[0]                   ),
    .l1_end_addr_i        ( cl_end_addr[NUM_CLUSTERS-1]        ),
    .host_req_i           ( host_wide_req_i                    ),
    .host_resp_o          ( host_wide_resp_o                   ),
    .ni_req_i             ( ni_wide_req_i                      ),
    .ni_resp_o            ( ni_wide_resp_o                     ),
    .no_req_i             ( no_wide_req_i                      ),
    .no_resp_o            ( no_wide_resp_o                     ),
    .edma_req_i           ( nhi_mst_edma_req                   ),
    .edma_resp_o          ( nhi_mst_edma_resp                  ),
    .l2_hnd_req_o         ( l2_hnd_req_b                       ),
    .l2_hnd_resp_i        ( l2_hnd_resp_b                      ),
    .l2_pkt_req_o         ( l2_pkt_req_b                       ),
    .l2_pkt_resp_i        ( l2_pkt_resp_b                      ),
    .l2_prog_req_o        ( host_l2_prog_req                   ),
    .l2_prog_resp_i       ( host_l2_prog_resp                  ),
    .cluster_req_o        ( nhi_req                            ),
    .cluster_resp_i       ( nhi_resp                           )
  );

  // L2 crossbar 
  l2_xbar #(
    .AddrWidth  (AXI_SOC_AW),
    .DataWidth  (AXI_WIDE_DW),
    .IdWidth    (AXI_IW),
    .UserWidth  (AXI_UW),
    .req_t      (soc_wide_req_t),
    .resp_t     (soc_wide_resp_t)
  ) i_l2_xbar (
    .clk_i,
    .rst_ni,
    .l2_hnd_start_addr_i  (L2_HND_ADDR_START[AXI_SOC_AW-1:0] ),
    .l2_hnd_end_addr_i    (L2_HND_ADDR_END[AXI_SOC_AW-1:0]   ),
    .l2_pkt_start_addr_i  (L2_PKT_ADDR_START[AXI_SOC_AW-1:0] ),
    .l2_pkt_end_addr_i    (L2_PKT_ADDR_END[AXI_SOC_AW-1:0]   ),
    .pe_req_i             (pe_l2d_req                        ),
    .pe_resp_o            (pe_l2d_resp                       ),
    .dma_req_i            (dma_l2_req                        ),
    .dma_resp_o           (dma_l2_resp                       ),
    .l2_hnd_req_o         (l2_hnd_req_a                      ),
    .l2_hnd_resp_i        (l2_hnd_resp_a                     ),
    .l2_pkt_req_o         (l2_pkt_req_a                      ),
    .l2_pkt_resp_i        (l2_pkt_resp_a                     )
  );

  
  `ASSERT_INIT(max_clusters, NUM_CLUSTERS <= 65536);
  `ASSERT_INIT(max_cores, snitch_cluster_cfg_pkg::NrCores <= 65536);
  
endmodule