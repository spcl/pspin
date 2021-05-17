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

package automatic pspin_cfg_pkg;

  localparam int unsigned       NUM_CLUSTERS                = 4;    // number of clusters
  localparam int unsigned       NUM_CORES                   = 8;    // number of cores per cluster

  // AXI
  localparam int unsigned       AXI_SOC_AW                  = 48;   // [bit]
  localparam int unsigned       AXI_HOST_AW                 = 64;   // [bit]
  localparam int unsigned       AXI_WIDE_DW                 = 512;  // [bit], must be a power of 2
  localparam int unsigned       AXI_NARROW_DW               = 64;   // [bit], must be a power of 2
  localparam int unsigned       AXI_IW                      = 6;    // [bit]
  localparam int unsigned       AXI_UW                      = 4;    // [bit]

  // SOC DMA
  localparam int unsigned       SOC_DMA_AXI_REQ_DEPTH       = 12;   // tune me!
  localparam int unsigned       SOC_DMA_REQ_FIFO_DEPT       = 64;   // tune me!

  // MPQ engine
  localparam int unsigned       NUM_MPQ                     = 1024;
  localparam int unsigned       NUM_MPQ_CELLS               = 128;
  localparam int unsigned       NUM_MPQ_STATIC_CELLS        = 1; //per MPQ

  // Constants used for decoding HER info
  localparam int unsigned       C_SIZE_WIDTH                = 32;   
  localparam int unsigned       C_MSGID_WIDTH               = 10;
  localparam int unsigned       C_ADDR_WIDTH                = 32;
  localparam int unsigned       C_HOST_ADDR_WIDTH           = AXI_HOST_AW;

  // L1 organization
  localparam int unsigned       L1_CLUSTER_BASE             = 32'h1000_0000;
  localparam int unsigned       L1_CLUSTER_SPAN             = 32'h0040_0000; // address space reserved to a cluster is 4 MiB
  localparam int unsigned       L1_CLUSTER_SIZE             = 32'h0010_0000; // 1 MiB
  localparam int unsigned       L1_RUNTIME_OFFSET           = 32'h0000_0400; // 1 KiB reserved at the beginning.
  localparam int unsigned       L1_RUNTIME_SIZE             = 32'h0000_4000; // 16 KiB
  localparam int unsigned       L1_PKT_BUFF_OFFSET          = L1_RUNTIME_OFFSET + L1_RUNTIME_SIZE;
  localparam int unsigned       L1_PKT_BUFF_SIZE            = 32'h0001_0000; // 64 KiB
  localparam int unsigned       L1_SCRATCHPAD_OFFSET        = L1_PKT_BUFF_OFFSET + L1_PKT_BUFF_SIZE;
  localparam int unsigned       L1_SCRATCHPAD_SIZE          = L1_CLUSTER_SIZE - L1_PKT_BUFF_OFFSET;

  // Number of HERs that can be buffered (allows to overlap DMA transfer to running handlers)
  localparam int unsigned       BUFFERED_HERS_PER_CLUSTER   = 12;

  // the number of HERs in a cluster is the number of buffer ones + the ones running
  localparam int unsigned       NUM_HERS_PER_CLUSTER        = BUFFERED_HERS_PER_CLUSTER + NUM_CORES;

  // Max number of commands that an HPU can keep in flight
  localparam int unsigned       NUM_HPU_CMDS                = 4;

  //Number of command interfaces (NIC outbound, soc-level DMA) and IDs
  //NOTE: the IDs need to be consistent with the inputs of the cmd unit.
  localparam int unsigned       NUM_CMD_INTERFACES          = 3;
  localparam int unsigned       CMD_HOSTDIRECT_ID           = 0;
  localparam int unsigned       CMD_NIC_OUTBOUND_ID         = 1;
  localparam int unsigned       CMD_EDMA_ID                 = 2;

  // L2 sizing
  localparam int unsigned L2_HND_SIZE        = 32'h0040_0000;
  localparam int unsigned L2_HND_CUT_DW      = 64;
  localparam int unsigned L2_HND_CUT_N_WORDS = 16384;
  localparam int unsigned L2_HND_N_PAR_CUTS  = 32;

  localparam int unsigned L2_PKT_SIZE        = 32'h0040_0000;
  localparam int unsigned L2_PKT_CUT_DW      = 512;
  localparam int unsigned L2_PKT_CUT_N_WORDS = 2048;
  localparam int unsigned L2_PKT_N_PAR_CUTS  = 32;

  localparam int unsigned L2_PROG_SIZE       = 32'h0000_8000;

  // L2 address map
  localparam logic [AXI_SOC_AW-1:0] L2_HND_ADDR_START  = 48'h00_1C00_0000;
  localparam logic [AXI_SOC_AW-1:0] L2_HND_ADDR_END    = L2_HND_ADDR_START + L2_HND_SIZE - 1;

  localparam logic [AXI_SOC_AW-1:0] L2_PKT_ADDR_START  = 48'h00_1D00_0000;
  localparam logic [AXI_SOC_AW-1:0] L2_PKT_ADDR_END    = L2_PKT_ADDR_START + L2_PKT_SIZE - 1;
  
  localparam logic [AXI_SOC_AW-1:0] L2_PROG_ADDR_START = 48'h00_1E00_0000;
  localparam logic [AXI_SOC_AW-1:0] L2_PROG_ADDR_END = L2_PROG_ADDR_START + L2_PROG_SIZE - 1;

  localparam logic [AXI_SOC_AW-1:0] L2D_MIN_ADDR = L2_HND_ADDR_START;
  localparam logic [AXI_SOC_AW-1:0] L2D_MAX_ADDR = L2_PKT_ADDR_END;

  // Cluster and core ID widths
  localparam int unsigned HART_ID_WIDTH     = 16;
  localparam int unsigned CLUSTER_ID_WIDTH  = 16;

  // HPU driver address space (mmio)
  localparam logic [AXI_SOC_AW-1:0] HPU_DRIVER_BASE_ADDR = 48'h00_1b00_0000;
  localparam int HPU_DRIVER_SIZE = 1024;
  
  // Interface types
  typedef logic [AXI_SOC_AW-1:0]      addr_t;
  typedef logic [AXI_HOST_AW-1:0]     host_addr_t;
  typedef logic [AXI_WIDE_DW-1:0]     wide_data_t;
  typedef logic [AXI_WIDE_DW/8-1:0]   wide_strb_t;
  typedef logic [AXI_NARROW_DW-1:0]   narrow_data_t;
  typedef logic [AXI_NARROW_DW/8-1:0] narrow_strb_t;
  typedef logic [AXI_IW-1:0]          id_t;
  typedef logic [AXI_UW-1:0]          user_t;

  `AXI_TYPEDEF_ALL(soc_wide, addr_t, id_t, wide_data_t, wide_strb_t, user_t)
  `AXI_TYPEDEF_ALL(soc_narrow, addr_t, id_t, narrow_data_t, narrow_strb_t, user_t)
  `AXI_TYPEDEF_ALL(host_wide, host_addr_t, id_t, wide_data_t, wide_strb_t, user_t)

  // Scheduling types
  typedef logic [$clog2(NUM_HERS_PER_CLUSTER):0] cluster_occup_t;
  typedef logic [C_ADDR_WIDTH-1:0] pkt_ptr_t;
  typedef logic [C_ADDR_WIDTH-1:0] mem_addr_t;
  typedef logic [C_SIZE_WIDTH-1:0] mem_size_t;

  // feedback descriptor
  typedef struct packed {
    logic [C_ADDR_WIDTH-1:0]      pkt_addr;
    mem_size_t                    pkt_size;
    logic [C_MSGID_WIDTH-1:0]     msgid;
    logic                         trigger_feedback;
  } feedback_descr_t;

  // MPQ meta descriptor
  typedef struct packed {

    //handler memory
    mem_addr_t                    handler_mem_addr;
    mem_size_t                    handler_mem_size;

    //host memory
    host_addr_t                   host_mem_addr;
    mem_size_t                    host_mem_size;

    //header handler
    mem_addr_t                    hh_addr;
    mem_size_t                    hh_size;

    //payload handler
    mem_addr_t                    ph_addr;
    mem_size_t                    ph_size;

    //completion (aka tail) handler
    mem_addr_t                    th_addr;
    mem_size_t                    th_size;

    //L1 scratchpads
    mem_addr_t [NUM_CLUSTERS-1:0] scratchpad_addr;
    mem_size_t [NUM_CLUSTERS-1:0] scratchpad_size;

  } mpq_meta_t;

  // Handler execution request (HER)
  typedef struct packed {

    logic [C_MSGID_WIDTH-1:0]  msgid;

    logic                      eom;

    //full her descriptor
    mem_addr_t                 her_addr;
    mem_size_t                 her_size;
    mem_size_t                 xfer_size;

    mpq_meta_t                 mpq_meta;
  } her_descr_t;

  // Job descriptor (an HER can generate multiple jobs). This is what is
  // sent to the clusters.
  typedef struct packed {

    logic [C_MSGID_WIDTH-1:0]       msgid;

    mem_addr_t                      handler_fun;
    mem_size_t                      handler_fun_size;

    mem_addr_t                      handler_mem_addr;
    mem_size_t                      handler_mem_size;

    host_addr_t                     host_mem_addr;
    mem_size_t                      host_mem_size;

    mem_addr_t                      pkt_addr;
    mem_size_t                      pkt_size;

    logic                           trigger_feedback;

    mem_addr_t [NUM_CLUSTERS-1:0]   scratchpad_addr;
    mem_size_t [NUM_CLUSTERS-1:0]   scratchpad_size;

  } handler_task_t;

  // DMA transfer descriptor (32 bit addresses)
  typedef struct packed {
    logic [31:0] num_bytes;
    logic [31:0] dst_addr;
    logic [31:0] src_addr;
    logic        deburst;
    logic        decouple;
    logic        serialize;
  } transf_descr_32_t;

  // DMA transfer descriptor (64 bit addresses)
  typedef struct packed {
    logic [31:0] num_bytes;
    logic [65:0] dst_addr;
    logic [65:0] src_addr;
    logic        deburst;
    logic        decouple;
    logic        serialize;
  } transf_descr_64_t;

  // Task descriptor (sent by the local scheduler to the HPU driver)
  typedef struct packed {
    handler_task_t  handler_task;
    pkt_ptr_t       pkt_ptr;
  } hpu_handler_task_t;

  // Task feedback descriptor (sent by the HPU driver to the local scheduler)
  typedef struct packed {
    feedback_descr_t  feedback_descr;
    pkt_ptr_t         pkt_ptr;
  } task_feedback_descr_t;

  // a bit ugly but they are shared between the mpq_engine and the mpq_fsm, so not sure
  // how to share these two types differertly (except for passing both of them as parameters, which
  // would be ugly as well)
  typedef enum logic [2:0] {Free, Header, HeaderRunning, Payload, PayloadDraining, Completion, CompletionRunning} mpq_state_t;
  typedef struct packed {
      mpq_state_t                       state;
      logic [$clog2(NUM_MPQ_CELLS):0]   length;
      logic [$clog2(NUM_MPQ_CELLS):0]   in_flight;
      logic                             has_completion;
      logic                             eom_seen;
  } mpq_t;

  //////////////
  /* Commands */
  //////////////

  // network ID (e.g., IP address)
  typedef logic [31:0] nid_t;

  // flow ID (e.g., (srcport, dstport) or matching bits)
  typedef logic [31:0] fid_t;

  // memory type
  typedef enum logic [1:0] {HostMem, NicMem} mem_type_t;

  // userptr
  typedef logic [63:0] user_ptr_t;

  //NIC put/send command (224 b, padded to 76 B)
  typedef struct packed {
      logic [383:0] unused;     // 384b
      user_ptr_t    user_ptr;   // 64b
      mem_size_t    length;     // 32b
      host_addr_t   src_addr;   // 64b
      fid_t         fid;        // 32b unused
      nid_t         nid;        // 32b
  } nic_cmd_t;

  // Host <-> PsPIN DMA command (193 b, padded to 76 B)
  typedef struct packed {
      logic [414:0] unused;     // 415b
      user_ptr_t    user_ptr;   // 64b
      logic         nic_to_host;// 1
      mem_size_t    length;     // 32b
      mem_addr_t    nic_addr;   // 32b
      host_addr_t   host_addr;  // 64b
  } host_dma_cmd_t;

  // PsPIN <-> Host with immediate data (586 b, padded to 76 B)
  typedef struct packed {
    logic [AXI_WIDE_DW-1:0]               imm_data;       // 512b
    logic [21:0]                          unused;         // 22b
    logic [$clog2(AXI_WIDE_DW)-1:0]       imm_data_size;  // 9b
    logic                                 nic_to_host;    // 1b
    host_addr_t                           host_addr;      // 64b
  } host_direct_cmd_t;

  typedef union packed {
      logic [18:0][31:0] words; //TODO: determine this size programatically (max(sizeof(nic_cmd_t), sizeof(host_dma_cmd_t)))/32
      nic_cmd_t          nic_cmd;
      host_dma_cmd_t     host_dma_cmd;
      host_direct_cmd_t  host_direct_cmd;
  } pspin_cmd_descr_t;

  typedef enum logic [1:0] {HostMemCpy, NICSend, HostDirect} pspin_cmd_type_t;
  typedef logic [$clog2(NUM_CMD_INTERFACES)-1:0] pspin_cmd_intf_id_t;

  typedef struct packed {
    logic [$clog2(NUM_CLUSTERS)-1:0] cluster_id;
    logic [$clog2(NUM_CORES)-1:0] core_id;
    logic [$clog2(NUM_HPU_CMDS)-1:0] local_cmd_id;
  } pspin_cmd_id_t;

  typedef struct packed {
    pspin_cmd_intf_id_t intf_id;
    pspin_cmd_id_t cmd_id;
    pspin_cmd_type_t  cmd_type;
    pspin_cmd_descr_t descr;

    logic       generate_event;
  } pspin_cmd_req_t;

  typedef struct packed {
     pspin_cmd_id_t cmd_id;
     logic [AXI_WIDE_DW-1:0] imm_data;
  } pspin_cmd_resp_t;


endpackage
