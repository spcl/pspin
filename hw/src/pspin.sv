// Copyright (c) 2020 ETH Zurich and University of Bologna
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

module pspin #(
  parameter int unsigned N_CLUSTERS = 0,
  parameter int N_MPQ = 0
) (
  // Clocks and Resets
  input  logic                            clk_i,
  input  logic                            rst_ni,

  // Cluster Control
  input  logic [N_CLUSTERS-1:0]           cl_fetch_en_i, 
  output logic [N_CLUSTERS-1:0]           cl_eoc_o,
  output logic [N_CLUSTERS-1:0]           cl_busy_o,

  AXI_BUS.Slave                           axi_ni_slv,    //NIC inbound slave port: to inject packets
  AXI_BUS.Slave                           axi_no_slv,    //NIC outbound slave port: to read data to send out
  AXI_BUS.Master                          axi_host_mst,  // Host master port: to write to host memory
  AXI_BUS.Slave                           axi_host_slv,  // Host slave port: to let the host write to L2 prog mem and L2 handler mem

  //from pktgen
  output logic                            task_ready_o,
  input  logic                            task_valid_i,
  input  pspin_cfg_pkg::handler_task_t    task_i,
  
  //termination signal    
  input  logic                            eos_i,

  //MPQ full signal
  output logic [N_MPQ-1:0]                mpq_full_o,                      

  //to pktgen
  input  logic                            nic_feedback_ready_i,
  output logic                            nic_feedback_valid_o,
  output pspin_cfg_pkg::feedback_descr_t  nic_feedback_o,

  output logic                            pspin_active_o,

  input  logic                            nic_cmd_ready_i,
  output logic                            nic_cmd_valid_o,
  output pspin_cfg_pkg::pspin_cmd_t       nic_cmd_o,

  input logic                             nic_cmd_resp_valid_i,
  input pspin_cfg_pkg::pspin_cmd_resp_t   nic_cmd_resp_i
);

  import pspin_cfg_pkg::AXI_AW;
  import pspin_cfg_pkg::HOST_AXI_AW;
  import pspin_cfg_pkg::addr_t;
  import pspin_cfg_pkg::AXI_WIDE_DW;
  import pspin_cfg_pkg::data_t;
  import pspin_cfg_pkg::strb_t;
  import pspin_cfg_pkg::AXI_IW;
  import pspin_cfg_pkg::id_t;
  import pspin_cfg_pkg::AXI_UW;
  import pspin_cfg_pkg::user_t;
  import pspin_cfg_pkg::aw_t;
  import pspin_cfg_pkg::w_t;
  import pspin_cfg_pkg::b_t;
  import pspin_cfg_pkg::ar_t;
  import pspin_cfg_pkg::r_t;
  import pspin_cfg_pkg::req_t;
  import pspin_cfg_pkg::resp_t;
  import pspin_cfg_pkg::host_req_t;
  import pspin_cfg_pkg::host_resp_t;
  import pspin_cfg_pkg::L1_CLUSTER_BASE;
  import pspin_cfg_pkg::L1_CLUSTER_MEM_SIZE;
  localparam int unsigned L2_SIZE = pulp_cluster_cfg_pkg::L2_SIZE;

  // Interface from NIC inbound
  req_t   ni_req;
  resp_t  ni_resp;
  `AXI_ASSIGN_TO_REQ(ni_req, axi_ni_slv)
  `AXI_ASSIGN_FROM_RESP(axi_ni_slv, ni_resp)

  // Interface from NIC outbound
  req_t   no_req;
  resp_t  no_resp;
  `AXI_ASSIGN_TO_REQ(no_req, axi_no_slv)
  `AXI_ASSIGN_FROM_RESP(axi_no_slv, no_resp)

  // Interface to Host
  host_req_t   host_mst_req;
  host_resp_t  host_mst_resp;
  `AXI_ASSIGN_FROM_REQ(axi_host_mst, host_mst_req)
  `AXI_ASSIGN_TO_RESP(host_mst_resp, axi_host_mst)

  host_req_t   host_mst_soc_dma_req, host_mst_hdir_req;
  host_resp_t  host_mst_soc_dma_resp, host_mst_hdir_resp;

  // Interface from Host 
  req_t   host_slv_req;
  resp_t  host_slv_resp;
  `AXI_ASSIGN_TO_REQ(host_slv_req, axi_host_slv)
  `AXI_ASSIGN_FROM_RESP(axi_host_slv, host_slv_resp)

  // Interface from NHI interconnect to cluster noc
  req_t   nhi_req;
  resp_t  nhi_resp;

  // Interfaces to Clusters
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (pulp_cluster_cfg_pkg::AXI_DW),
    .AXI_ID_WIDTH   (pulp_cluster_cfg_pkg::AXI_IW_SLV),
    .AXI_USER_WIDTH (AXI_UW)
  ) cl_inp[N_CLUSTERS-1:0]();
  pulp_cluster_cfg_pkg::req_slv_t   [N_CLUSTERS-1:0]  cl_inp_req;
  pulp_cluster_cfg_pkg::resp_slv_t  [N_CLUSTERS-1:0]  cl_inp_resp;
  for (genvar i = 0; i < N_CLUSTERS; i++) begin : gen_assign_cl_inp
    `AXI_ASSIGN_FROM_REQ(cl_inp[i], cl_inp_req[i])
    `AXI_ASSIGN_TO_RESP(cl_inp_resp[i], cl_inp[i])
  end
  AXI_BUS_ASYNC #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (pulp_cluster_cfg_pkg::AXI_DW),
    .AXI_ID_WIDTH   (pulp_cluster_cfg_pkg::AXI_IW_SLV),
    .AXI_USER_WIDTH (AXI_UW),
    .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
  ) cl_inp_async[N_CLUSTERS-1:0]();

  // Interfaces from Clusters
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (pulp_cluster_cfg_pkg::AXI_DW),
    .AXI_ID_WIDTH   (pulp_cluster_cfg_pkg::AXI_IW_MST),
    .AXI_USER_WIDTH (AXI_UW)
  ) cl_oup[N_CLUSTERS-1:0]();
  pulp_cluster_cfg_pkg::req_mst_t   [N_CLUSTERS-1:0]  cl_oup_req;
  pulp_cluster_cfg_pkg::resp_mst_t  [N_CLUSTERS-1:0]  cl_oup_resp;
  for (genvar i = 0; i < N_CLUSTERS; i++) begin : gen_assign_cl_oup
    `AXI_ASSIGN_TO_REQ(cl_oup_req[i], cl_oup[i])
    `AXI_ASSIGN_FROM_RESP(cl_oup[i], cl_oup_resp[i])
  end
  AXI_BUS_ASYNC #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (pulp_cluster_cfg_pkg::AXI_DW),
    .AXI_ID_WIDTH   (pulp_cluster_cfg_pkg::AXI_IW_MST),
    .AXI_USER_WIDTH (AXI_UW),
    .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
  ) cl_oup_async[N_CLUSTERS-1:0]();

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (pulp_cluster_cfg_pkg::AXI_DMA_DW),
    .AXI_ID_WIDTH   (pulp_cluster_cfg_pkg::AXI_DMA_IW),
    .AXI_USER_WIDTH (AXI_UW)
  ) cl_dma[N_CLUSTERS-1:0]();
  pulp_cluster_cfg_pkg::req_dma_t   [N_CLUSTERS-1:0]  cl_dma_req;
  pulp_cluster_cfg_pkg::resp_dma_t  [N_CLUSTERS-1:0]  cl_dma_resp;
  for (genvar i = 0; i < N_CLUSTERS; i++) begin : gen_assign_cl_dma
    `AXI_ASSIGN_TO_REQ(cl_dma_req[i], cl_dma[i])
    `AXI_ASSIGN_FROM_RESP(cl_dma[i], cl_dma_resp[i])
  end
  AXI_BUS_ASYNC #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (pulp_cluster_cfg_pkg::AXI_DMA_DW),
    .AXI_ID_WIDTH   (pulp_cluster_cfg_pkg::AXI_DMA_IW),
    .AXI_USER_WIDTH (AXI_UW),
    .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
  ) cl_dma_async[N_CLUSTERS-1:0]();

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (pulp_cluster_cfg_pkg::AXI_DMA_DW),
    .AXI_ID_WIDTH   (pulp_cluster_cfg_pkg::AXI_DMA_IW),
    .AXI_USER_WIDTH (AXI_UW)
  ) cl_nhi[N_CLUSTERS-1:0]();
  pulp_cluster_cfg_pkg::req_dma_t   [N_CLUSTERS-1:0]  cl_nhi_req;
  pulp_cluster_cfg_pkg::resp_dma_t  [N_CLUSTERS-1:0]  cl_nhi_resp;
  for (genvar i = 0; i < N_CLUSTERS; i++) begin : gen_assign_cl_nhi
    `AXI_ASSIGN_FROM_REQ(cl_nhi[i], cl_nhi_req[i])
    `AXI_ASSIGN_TO_RESP(cl_nhi_resp[i], cl_nhi[i])
  end
  /* We are not using async clusters, can we remove their definition? */
  /*
  AXI_BUS_ASYNC #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (pulp_cluster_cfg_pkg::AXI_DMA_DW),
    .AXI_ID_WIDTH   (pulp_cluster_cfg_pkg::AXI_DMA_IW),
    .AXI_USER_WIDTH (AXI_UW),
    .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
  ) cl_nhi_async[N_CLUSTERS-1:0]();
  */
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (pulp_cluster_cfg_pkg::AXI_DW_ICACHE),
    .AXI_ID_WIDTH   (pulp_cluster_cfg_pkg::AXI_IW_ICACHE),
    .AXI_USER_WIDTH (AXI_UW)
  ) cl_icache[N_CLUSTERS-1:0]();
  
  pulp_cluster_cfg_pkg::req_icache_t   [N_CLUSTERS-1:0]  cl_icache_req;
  pulp_cluster_cfg_pkg::resp_icache_t  [N_CLUSTERS-1:0]  cl_icache_resp;

  pulp_cluster_cfg_pkg::req_icache_t  host_slv_downsized_req;
  pulp_cluster_cfg_pkg::resp_icache_t host_slv_downsized_resp;

  for (genvar i = 0; i < N_CLUSTERS; i++) begin : gen_assign_cl_icache
    `AXI_ASSIGN_TO_REQ(cl_icache_req[i], cl_icache[i])
    `AXI_ASSIGN_FROM_RESP(cl_icache[i], cl_icache_resp[i])
  end
  AXI_BUS_ASYNC #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (pulp_cluster_cfg_pkg::AXI_DW_ICACHE),
    .AXI_ID_WIDTH   (pulp_cluster_cfg_pkg::AXI_IW_ICACHE),
    .AXI_USER_WIDTH (AXI_UW),
    .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
  ) cl_icache_async[N_CLUSTERS-1:0]();

  // Interfaces to L2 Memory
  req_t   pe_l2_req,  dma_l2_req,   l2_hnd_req_a,  l2_hnd_req_b,  l2_pkt_req_a,  l2_pkt_req_b;
  resp_t  pe_l2_resp, dma_l2_resp,  l2_hnd_resp_a, l2_hnd_resp_b, l2_pkt_resp_a, l2_pkt_resp_b;
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
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
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_WIDE_DW),
    .AXI_ID_WIDTH   (AXI_IW),
    .AXI_USER_WIDTH (AXI_UW)
  ) l2_hnd_mst_wo_atomics();

  req_t host_l2_prog_req;
  resp_t host_l2_prog_resp;

  // Interface from eDMA to NHI
  req_t nhi_mst_edma_req;
  resp_t nhi_mst_edma_resp;
 
  // Interfaces to Peripherals
  localparam int unsigned AXI_DW_PERIPHS = 64;
  typedef logic [AXI_DW_PERIPHS-1:0]    periph_data_t;
  typedef logic [AXI_DW_PERIPHS/8-1:0]  periph_strb_t;
  `AXI_TYPEDEF_W_CHAN_T(periph_w_t, periph_data_t, periph_strb_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(periph_r_t, periph_data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(periph_req_t, aw_t, periph_w_t, ar_t)
  `AXI_TYPEDEF_RESP_T(periph_resp_t, b_t, periph_r_t)
  periph_req_t  periph_req;
  periph_resp_t periph_resp;
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW_PERIPHS),
    .AXI_ID_WIDTH   (AXI_IW),
    .AXI_USER_WIDTH (AXI_UW)
  ) periph_mst();
  `AXI_ASSIGN_FROM_REQ(periph_mst, periph_req)
  `AXI_ASSIGN_TO_RESP(periph_resp, periph_mst)

  // mpq_engine -> scheduler
  // logic                                       mpqengine_scheduler_valid;
  // logic                                       mpqengine_scheduler_ready;
  // pspin_cfg_pkg::handler_task_t                   mpqengine_scheduler_task;

  // scheduler -> mpq_engine
  logic                                       scheduler_mpqengine_valid;
  logic                                       scheduler_mpqengine_ready;
  pspin_cfg_pkg::feedback_descr_t                 scheduler_mpqengine_feedback;

  // scheduler -> cluster_schedulers
  logic [N_CLUSTERS-1:0]                            sched_loc_valid;
  logic [N_CLUSTERS-1:0]                            sched_loc_ready;
  pspin_cfg_pkg::handler_task_t [N_CLUSTERS-1:0]    sched_loc_task;

  // cluster_schedulers -> scheduler 
  logic [N_CLUSTERS-1:0]                            loc_sched_valid;
  logic [N_CLUSTERS-1:0]                            loc_sched_ready;
  pspin_cfg_pkg::feedback_descr_t [N_CLUSTERS-1:0]  loc_sched_feedback;

  logic [N_CLUSTERS-1:0]                            cluster_active_q;
  logic [N_CLUSTERS-1:0]                            cluster_active_d;

  logic [N_CLUSTERS-1:0]                            cluster_cmd_ready;
  logic [N_CLUSTERS-1:0]                            cluster_cmd_valid;
  pspin_cfg_pkg::pspin_cmd_t [N_CLUSTERS-1:0]       cluster_cmd;

  logic                                             cluster_cmd_resp_valid;
  pspin_cfg_pkg::pspin_cmd_resp_t                   cluster_cmd_resp;

  // CMD unit <-> soc-level DMA
  logic                                             edma_cmd_ready;
  logic                                             edma_cmd_valid;
  pspin_cfg_pkg::pspin_cmd_t                        edma_cmd;
  logic                                             edma_resp_valid;
  pspin_cfg_pkg::pspin_cmd_resp_t                   edma_resp;

  // CMD unit <-> HostDirect unit
  logic                                             hdir_cmd_valid;
  logic                                             hdir_cmd_ready;
  pspin_cfg_pkg::pspin_cmd_t                        hdir_cmd;
  logic                                             hdir_resp_valid;
  pspin_cfg_pkg::pspin_cmd_resp_t                   hdir_resp;
  
  assign pspin_active_o = (~cluster_active_q == '0);

  // mpq_engine #(
  //   .NUM_HER_SLOTS          (pspin_cfg_pkg::NUM_MPQ_CELLS),
  //   .NUM_MPQ                (N_MPQ) 
  // ) i_mpq_engine (
  //   .rst_ni                 (rst_ni),
  //   .clk_i                  (clk_i),

  //   .her_ready_o            (her_ready_o),
  //   .her_valid_i            (her_valid_i),
  //   .her_i                  (her_i),

  //   .eos_i                  (eos_i),

  //   .mpq_full_o             (mpq_full_o),

  //   .nic_feedback_ready_i   (nic_feedback_ready_i),
  //   .nic_feedback_valid_o   (nic_feedback_valid_o),
  //   .nic_feedback_o         (nic_feedback_o),

  //   .feedback_ready_o       (scheduler_mpqengine_ready),
  //   .feedback_valid_i       (scheduler_mpqengine_valid),
  //   .feedback_i             (scheduler_mpqengine_feedback),

  //   .task_ready_i           (mpqengine_scheduler_ready),
  //   .task_valid_o           (mpqengine_scheduler_valid),
  //   .task_o                 (mpqengine_scheduler_task)

  // );

  scheduler #(
    .NUM_CLUSTERS             (N_CLUSTERS),
    .NUM_HERS_PER_CLUSTER     (pspin_cfg_pkg::NUM_HERS_PER_CLUSTER)
  ) i_scheduler (
    .rst_ni                   (rst_ni),
    .clk_i                    (clk_i),

    //from MPQ engine
    .task_valid_i             (task_valid_i),
    .task_ready_o             (task_ready_o),
    .task_descr_i             (task_i),

    // to MPQ engine (TODO: change names)
    .pktgen_feedback_valid_o  (nic_feedback_valid_o),
    .pktgen_feedback_ready_i  (nic_feedback_ready_i),
    .pktgen_feedback_o        (nic_feedback_o),

    // to cluster_schedulers
    .cluster_task_valid_o     (sched_loc_valid),
    .cluster_task_ready_i     (sched_loc_ready),
    .cluster_task_descr_o     (sched_loc_task),

    // from cluster schedulers
    .cluster_feedback_valid_i (loc_sched_valid),
    .cluster_feedback_ready_o (loc_sched_ready),
    .cluster_feedback_i       (loc_sched_feedback)
  );

  soc_dma_wrap #(
    .DmaAxiIdWidth     (AXI_IW),
    .DmaDataWidth      (AXI_WIDE_DW),
    .DmaUserWidth      (AXI_UW),
    .AxiAxReqDepth     (pspin_cfg_pkg::SOC_DMA_AXI_REQ_DEPTH),
    .TfReqFifoDepth    (pspin_cfg_pkg::SOC_DMA_REQ_FIFO_DEPT),
    .axi_nhi_req_t     (req_t),
    .axi_nhi_res_t     (resp_t),
    .axi_host_req_t    (host_req_t),
    .axi_host_res_t    (host_resp_t)
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

  host_direct #(
    .AXI_AW             (HOST_AXI_AW),
    .AXI_DW             (AXI_WIDE_DW),
    .CMD_IMM_DATA_SIZE  (AXI_WIDE_DW),
    .axi_host_aw_t      (pspin_cfg_pkg::aw_host_t),
    .axi_host_ar_t      (pspin_cfg_pkg::ar_host_t),
    .axi_host_w_t       (pspin_cfg_pkg::w_t),
    .axi_host_r_t       (pspin_cfg_pkg::r_t),
    .axi_host_b_t       (pspin_cfg_pkg::b_t),
    .axi_host_req_t     (host_req_t),
    .axi_host_res_t     (host_resp_t),
    .cmd_req_t          (pspin_cfg_pkg::pspin_cmd_t),
    .cmd_res_t          (pspin_cfg_pkg::pspin_cmd_resp_t),
    .cmd_id_t           (pspin_cfg_pkg::pspin_cmd_id_t)
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

  host_mst_mux #(
    .AddrWidth          (HOST_AXI_AW),
    .DataWidth          (AXI_WIDE_DW),
    .IdWidth            (AXI_IW),
    .UserWidth          (AXI_UW),
    .req_t              (host_req_t),
    .resp_t             (host_resp_t)
  ) i_mux_host_mst (
    .clk_i              (clk_i),
    .rst_ni             (rst_ni),

    .dma_req_i          (host_mst_soc_dma_req),
    .dma_resp_o         (host_mst_soc_dma_resp),

    .hdir_req_i         (host_mst_hdir_req),
    .hdir_resp_o        (host_mst_hdir_resp),
    
    .host_req_o         (host_mst_req),
    .host_resp_i        (host_mst_resp)
  );

  cmd_unit #(
    .NUM_CLUSTERS                (N_CLUSTERS),
    .NUM_CMD_INTERFACES          (pspin_cfg_pkg::NUM_CMD_INTERFACES)
  ) i_cmd_unit (
    .rst_ni                      (rst_ni),
    .clk_i                       (clk_i),

    //commands from clusters
    .cmd_ready_o                 (cluster_cmd_ready),
    .cmd_valid_i                 (cluster_cmd_valid),
    .cmd_i                       (cluster_cmd),

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

  for (genvar i = 0; i < N_CLUSTERS; i++) begin: gen_clusters
    logic [5:0] cluster_id;
    assign cluster_id = i;

    if (pulp_cluster_cfg_pkg::ASYNC) begin : gen_cluster_async
      axi_slice_dc_slave_wrap #(
        .AXI_ADDR_WIDTH (AXI_AW),
        .AXI_DATA_WIDTH (pulp_cluster_cfg_pkg::AXI_DW),
        .AXI_USER_WIDTH (AXI_UW),
        .AXI_ID_WIDTH   (pulp_cluster_cfg_pkg::AXI_IW_SLV),
        .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
      ) i_dc_slice_cl_inp (
        .clk_i,
        .rst_ni,
        .test_cgbypass_i  (1'b0),
        .isolate_i        (1'b0),
        .axi_slave        (cl_inp[i]),
        .axi_master_async (cl_inp_async[i])
      );
      pulp_cluster_async i_cluster (
        .clk_i,
        .rst_ni,
        .ref_clk_i    (clk_i),
        .cluster_id_i (cluster_id),
        .fetch_en_i   (cl_fetch_en_i[i]),
        .eoc_o        (cl_eoc_o[i]),
        .busy_o       (cl_busy_o[i]),
        .slv          (cl_inp_async[i]),
        .mst          (cl_oup_async[i]),
        .dma          (cl_dma_async[i]),
        .icache       (cl_icache_async[i])
      );
      axi_slice_dc_master_wrap #(
        .AXI_ADDR_WIDTH (AXI_AW),
        .AXI_DATA_WIDTH (pulp_cluster_cfg_pkg::AXI_DW),
        .AXI_USER_WIDTH (AXI_UW),
        .AXI_ID_WIDTH   (pulp_cluster_cfg_pkg::AXI_IW_MST),
        .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
      ) i_dc_slice_cl_oup (
        .clk_i,
        .rst_ni,
        .test_cgbypass_i  (1'b0),
        .clock_down_i     (1'b0),
        .isolate_i        (1'b0),
        .incoming_req_o   (),
        .axi_slave_async  (cl_oup_async[i]),
        .axi_master       (cl_oup[i])
      );
      axi_slice_dc_master_wrap #(
        .AXI_ADDR_WIDTH (AXI_AW),
        .AXI_DATA_WIDTH (pulp_cluster_cfg_pkg::AXI_DMA_DW),
        .AXI_USER_WIDTH (AXI_UW),
        .AXI_ID_WIDTH   (pulp_cluster_cfg_pkg::AXI_DMA_IW),
        .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
      ) i_dc_slice_cl_dma (
        .clk_i,
        .rst_ni,
        .test_cgbypass_i  (1'b0),
        .clock_down_i     (1'b0),
        .isolate_i        (1'b0),
        .incoming_req_o   (),
        .axi_slave_async  (cl_dma_async[i]),
        .axi_master       (cl_dma[i])
      );

    end else begin : gen_cluster_sync
      pulp_cluster_sync i_cluster (
        .clk_i,
        .rst_ni,
        .ref_clk_i    (clk_i),
        .cluster_id_i (cluster_id),
        .fetch_en_i   (cl_fetch_en_i[i]),
        .eoc_o        (cl_eoc_o[i]),
        .busy_o       (cl_busy_o[i]),
        .slv          (cl_inp[i]),
        .mst          (cl_oup[i]),
        .dma          (cl_dma[i]),
        .icache       (cl_icache[i]),
        .nhi          (cl_nhi[i]),

        .task_valid_i         (sched_loc_valid[i]),
        .task_ready_o         (sched_loc_ready[i]),
        .task_descr_i         (sched_loc_task[i]),
        .feedback_valid_o     (loc_sched_valid[i]),
        .feedback_ready_i     (loc_sched_ready[i]),
        .feedback_o           (loc_sched_feedback[i]),
        .cluster_active_o     (cluster_active_d[i]),
        .cmd_ready_i          (cluster_cmd_ready[i]),
        .cmd_valid_o          (cluster_cmd_valid[i]),
        .cmd_o                (cluster_cmd[i]),
        .cmd_resp_valid_i     (cluster_cmd_resp_valid),
        .cmd_resp_i           (cluster_cmd_resp)
      );
    end
  end

  /// Address map
  // Clusters
  addr_t [N_CLUSTERS-1:0] cl_start_addr, cl_end_addr;
  for (genvar i = 0; i < N_CLUSTERS; i++) begin : gen_map_clusters
      assign cl_start_addr[i] = L1_CLUSTER_BASE +  i    * L1_CLUSTER_MEM_SIZE;
      assign cl_end_addr[i]   = L1_CLUSTER_BASE + (i+1) * L1_CLUSTER_MEM_SIZE;
  end
  // L2
  addr_t  l2_hnd_start_addr,  l2_hnd_end_addr,
          l2_pkt_start_addr,  l2_pkt_end_addr,
          l2_prog_start_addr, l2_prog_end_addr,
          l2_start_addr,      l2_end_addr;
  assign l2_hnd_start_addr  = 32'h1C00_0000;
  assign l2_hnd_end_addr    = l2_hnd_start_addr + addr_t'(pspin_cfg_pkg::MEM_HND_SIZE);

  assign l2_pkt_start_addr  = l2_hnd_end_addr;
  assign l2_pkt_end_addr    = l2_pkt_start_addr + addr_t'(pspin_cfg_pkg::MEM_PKT_SIZE);
  
  assign l2_prog_start_addr = 32'h1D00_0000;
  assign l2_prog_end_addr   = l2_prog_start_addr + 32'h0000_8000;
  
  assign l2_start_addr      = l2_hnd_start_addr;
  assign l2_end_addr        = l2_pkt_end_addr;
  
  // Peripherals
  addr_t periph_start_addr, periph_end_addr;
  assign periph_start_addr  = 32'h1A10_0000;
  assign periph_end_addr    = periph_start_addr + addr_t'(32*1024);

  prog_mem #(
    .NumClusters  (N_CLUSTERS),
    .NumBytes     (pspin_cfg_pkg::MEM_PROG_SIZE),
    .AddrWidth    (AXI_AW),
    .DataWidth    (pulp_cluster_cfg_pkg::AXI_DW_ICACHE),
    .IdWidth      (pulp_cluster_cfg_pkg::AXI_IW_ICACHE),
    .UserWidth    (AXI_UW),
    .req_t        (pulp_cluster_cfg_pkg::req_icache_t),
    .resp_t       (pulp_cluster_cfg_pkg::resp_icache_t)
  ) i_prog_mem (
    .clk_i,
    .rst_ni,
    .cl_req_i     ( cl_icache_req           ),
    .cl_resp_o    ( cl_icache_resp          ),
    .host_req_i   ( host_slv_downsized_req  ),
    .host_resp_o  ( host_slv_downsized_resp )
  );

  pe_noc #(
    .NumClusters      (N_CLUSTERS),
    .AddrWidth        (AXI_AW),
    .ClDataWidth      (pulp_cluster_cfg_pkg::AXI_DW),
    .ClOupIdWidth     (pulp_cluster_cfg_pkg::AXI_IW_MST),
    .ClInpIdWidth     (pulp_cluster_cfg_pkg::AXI_IW_SLV),
    .L2DataWidth      (AXI_WIDE_DW),
    .L2IdWidth        (AXI_IW),
    .PeriphDataWidth  (AXI_DW_PERIPHS),
    .PeriphIdWidth    (AXI_IW),
    .UserWidth        (AXI_UW),
    .cl_oup_req_t     (pulp_cluster_cfg_pkg::req_mst_t),
    .cl_oup_resp_t    (pulp_cluster_cfg_pkg::resp_mst_t),
    .cl_inp_req_t     (pulp_cluster_cfg_pkg::req_slv_t),
    .cl_inp_resp_t    (pulp_cluster_cfg_pkg::resp_slv_t),
    .l2_req_t         (req_t),
    .l2_resp_t        (resp_t),
    .periph_req_t     (periph_req_t),
    .periph_resp_t    (periph_resp_t)
  ) i_pe_noc (
    .clk_i,
    .rst_ni,
    .cl_start_addr_i      (cl_start_addr),
    .cl_end_addr_i        (cl_end_addr),
    .l2_start_addr_i      (l2_start_addr),
    .l2_end_addr_i        (l2_end_addr),
    .periph_start_addr_i  (periph_start_addr),
    .periph_end_addr_i    (periph_end_addr),
    .from_cl_req_i        (cl_oup_req),
    .from_cl_resp_o       (cl_oup_resp),
    .to_cl_req_o          (cl_inp_req),
    .to_cl_resp_i         (cl_inp_resp),
    .l2_req_o             (pe_l2_req),
    .l2_resp_i            (pe_l2_resp),
    .periph_req_o         (periph_req),
    .periph_resp_i        (periph_resp)
  );

  dma_noc #(
    .NumClusters  (N_CLUSTERS),
    .AddrWidth    (AXI_AW),
    .DataWidth    (AXI_WIDE_DW),
    .DMAIdWidth   (pulp_cluster_cfg_pkg::AXI_DMA_IW),
    .L2IdWidth    (AXI_IW),
    .UserWidth    (AXI_UW),
    .dma_req_t    (pulp_cluster_cfg_pkg::req_dma_t),
    .dma_resp_t   (pulp_cluster_cfg_pkg::resp_dma_t),
    .l2_req_t     (req_t),
    .l2_resp_t    (resp_t)
  ) i_dma_noc (
    .clk_i,
    .rst_ni,
    .l2_start_addr_i(l2_start_addr),
    .l2_end_addr_i  (l2_end_addr),
    .dma_req_i      (cl_dma_req),
    .dma_resp_o     (cl_dma_resp),
    .l2_req_o       (dma_l2_req),
    .l2_resp_i      (dma_l2_resp)
  );

  cluster_noc #(
    .NumClusters  (N_CLUSTERS),
    .AddrWidth    (AXI_AW),
    .DataWidth    (AXI_WIDE_DW),
    .UserWidth    (AXI_UW),
    .NHIIdWidth   (AXI_IW),
    .ClIdWidth    (pulp_cluster_cfg_pkg::AXI_DMA_IW),
    .nhi_req_t    (req_t),
    .nhi_resp_t   (resp_t),
    .cl_req_t     (pulp_cluster_cfg_pkg::req_dma_t),
    .cl_resp_t    (pulp_cluster_cfg_pkg::resp_dma_t)
  ) i_cluster_noc (
    .clk_i,
    .rst_ni,
    .cl_start_addr_i (cl_start_addr),
    .cl_end_addr_i   (cl_end_addr),
    .cl_req_o        (cl_nhi_req),
    .cl_resp_i       (cl_nhi_resp),
    .nhi_req_i       (nhi_req),
    .nhi_resp_o      (nhi_resp)
  );

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

  nhi_xbar #(
    .AddrWidth  (AXI_AW),
    .DataWidth  (AXI_WIDE_DW),
    .IdWidth    (AXI_IW),
    .UserWidth  (AXI_UW),
    .req_t      (req_t),
    .resp_t     (resp_t)
  ) i_nhi_xbar (
    .clk_i,
    .rst_ni,
    .l2_hnd_start_addr_i  ( l2_hnd_start_addr          ),
    .l2_hnd_end_addr_i    ( l2_hnd_end_addr            ),
    .l2_pkt_start_addr_i  ( l2_pkt_start_addr          ),
    .l2_pkt_end_addr_i    ( l2_pkt_end_addr            ),
    .l2_prog_start_addr_i ( l2_prog_start_addr         ),
    .l2_prog_end_addr_i   ( l2_prog_end_addr           ),
    .l1_start_addr_i      ( cl_start_addr[0]           ),
    .l1_end_addr_i        ( cl_end_addr[N_CLUSTERS-1]  ),
    .host_req_i           ( host_slv_req               ),
    .host_resp_o          ( host_slv_resp              ),
    .ni_req_i             ( ni_req                     ),
    .ni_resp_o            ( ni_resp                    ),
    .no_req_i             ( no_req                     ),
    .no_resp_o            ( no_resp                    ),
    .edma_req_i           ( nhi_mst_edma_req           ),
    .edma_resp_o          ( nhi_mst_edma_resp          ),
    .l2_hnd_req_o         ( l2_hnd_req_b               ),
    .l2_hnd_resp_i        ( l2_hnd_resp_b              ),
    .l2_pkt_req_o         ( l2_pkt_req_b               ),
    .l2_pkt_resp_i        ( l2_pkt_resp_b              ),
    .l2_prog_req_o        ( host_l2_prog_req           ),
    .l2_prog_resp_i       ( host_l2_prog_resp          ),
    .cluster_req_o        ( nhi_req                    ),
    .cluster_resp_i       ( nhi_resp                   )
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
  
  l2_mem #(
    .AXI_AW         (AXI_AW),
    .AXI_DW         (AXI_WIDE_DW),
    .AXI_UW         (AXI_UW),
    .AXI_IW         (AXI_IW),
    .N_BYTES        (pspin_cfg_pkg::MEM_HND_SIZE),
    .CUT_DW         (pspin_cfg_pkg::MEM_HND_CUT_DW),
    .CUT_N_WORDS    (pspin_cfg_pkg::MEM_HND_CUT_N_WORDS),
    .N_PAR_CUTS     (pspin_cfg_pkg::MEM_HND_N_PAR_CUTS)
  ) i_l2_hnd_mem (
    .clk_i,
    .rst_ni,
    .slv_a          (l2_hnd_mst_wo_atomics),
    .slv_b          (l2_hnd_mst_b)
  );

  l2_mem #(
    .AXI_AW         (AXI_AW),
    .AXI_DW         (AXI_WIDE_DW),
    .AXI_UW         (AXI_UW),
    .AXI_IW         (AXI_IW),
    .N_BYTES        (pspin_cfg_pkg::MEM_PKT_SIZE),
    .CUT_DW         (pspin_cfg_pkg::MEM_PKT_CUT_DW),
    .CUT_N_WORDS    (pspin_cfg_pkg::MEM_PKT_CUT_N_WORDS),
    .N_PAR_CUTS     (pspin_cfg_pkg::MEM_PKT_N_PAR_CUTS)
  ) i_l2_pkt_mem (
    .clk_i,
    .rst_ni,
    .slv_a          (l2_pkt_mst_a),
    .slv_b          (l2_pkt_mst_b)
  );

  soc_peripherals #(
    .AXI_AW     (AXI_AW),
    .AXI_IW     (AXI_IW),
    .AXI_UW     (AXI_UW),
    .N_CORES    (pulp_cluster_cfg_pkg::N_CORES),
    .N_CLUSTERS (N_CLUSTERS)
  ) i_periphs (
    .clk_i,
    .rst_ni,
    .test_en_i  ('0),
    .axi        (periph_mst)
  );

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      cluster_active_q <= '0;
    end else begin
      cluster_active_q <= cluster_active_d;
    end
  end

endmodule
