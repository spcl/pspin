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
 * core_region.sv
 * Davide Rossi <davide.rossi@unibo.it>
 * Antonio Pullini <pullinia@iis.ee.ethz.ch>
 * Igor Loi <igor.loi@unibo.it>
 * Francesco Conti <fconti@iis.ee.ethz.ch>
 */

import apu_package::*;

/* verilator tracing_on */

// USER DEFINED MACROS to improve self-testing capabilities
`ifndef PULP_FPGA_SIM
  `define DEBUG_FETCH_INTERFACE
`endif
//`define DATA_MISS
//`define DUMP_INSTR_FETCH

module core_region
#(
  // CORE PARAMETERS
  parameter int     CORE_ID                 = 0,
  parameter int     ADDR_WIDTH              = 32,
  parameter int     DATA_WIDTH              = 32,
  parameter int     INSTR_RDATA_WIDTH       = 32,
  parameter bit     CLUSTER_ALIAS           = 1'b1,
  parameter int     CLUSTER_ALIAS_BASE      = 12'h000,
  parameter int     REMAP_ADDRESS           = 0,
  parameter bit     DEM_PER_BEFORE_TCDM_TS  = 1'b0,
  parameter int     INTER_CORE_FIFO_DEPTH   = 0,
  parameter int     N_PMP_ENTRIES           = 16,
  parameter bit     USE_STORE_BUFFER        = 1'b0
`ifndef SYNTHESIS
  ,
  parameter string  L2_SLM_FILE   = "./slm_files/l2_stim.slm",
  parameter string  ROM_SLM_FILE  = "../sw/apps/boot/slm_files/l2_stim.slm"
`endif
)
(
  input logic 			      clk_i,
  input logic 			      rst_ni,
  input logic 			      init_ni,

  input logic [3:0] 		      base_addr_i, // FOR CLUSTER VIRTUALIZATION

  input logic [5:0] 		      cluster_id_i,
  
  input logic 			      irq_req_i,
  output logic 			      irq_ack_o,
  input logic [4:0] 		      irq_id_i,
  output logic [4:0] 		      irq_ack_id_o,

  input logic 			      clock_en_i,
  input logic 			      fetch_en_i,
  input logic 			      fregfile_disable_i,

  input logic [31:0] 		      boot_addr_i,

  input logic 			      test_mode_i,

  output logic 			      core_busy_o,

  // Interface to Instruction Logarithmic interconnect (Req->grant handshake)
  output logic 			      instr_req_o,
  input logic 			      instr_gnt_i,
  output logic [31:0] 		      instr_addr_o,
  input logic [INSTR_RDATA_WIDTH-1:0] instr_r_rdata_i,
  input logic 			      instr_r_valid_i,
				      
				      XBAR_TCDM_BUS.Slave debug_bus,
  output logic 			      debug_core_halted_o,
  input logic 			      debug_core_halt_i,
  input logic 			      debug_core_resume_i,
				      
  output logic            unaligned_o,

				      // Interface for DEMUX to TCDM INTERCONNECT ,PERIPHERAL INTERCONNECT and DMA CONTROLLER
				      XBAR_TCDM_BUS.Master tcdm_data_master,
				      output logic [5:0]     tcdm_data_master_atop,
				      XBAR_TCDM_BUS.Master dma_ctrl_master,
				      XBAR_PERIPH_BUS.Master eu_ctrl_master,
				      XBAR_PERIPH_BUS.Master periph_data_master,
				      output logic [5:0]     periph_data_master_atop,
				      
				      XBAR_PERIPH_BUS.Slave  this_fifo_slave,
				      XBAR_PERIPH_BUS.Master next_fifo_master,

				      XBAR_PERIPH_BUS.Master hpu_driver_master,

				      // APU interconnect interface
				      cpu_marx_if.cpu apu_master,

  //interface for configuring PMP from external
  input  logic pmp_conf_override_i,
  input  logic [N_PMP_ENTRIES-1:0] [31:0] pmp_addr_i,
  input  logic [N_PMP_ENTRIES-1:0] [7:0]  pmp_cfg_i
);

  XBAR_DEMUX_BUS    s_core_bus();         // Internal interface between CORE       <--> DEMUX
  XBAR_PERIPH_BUS   periph_demux_bus();   // Internal interface between CORE_DEMUX <--> PERIPHERAL DEMUX
  XBAR_PERIPH_BUS   this_fifo();
  XBAR_PERIPH_BUS   periph_data(), periph_data_buf();

  logic       core_buffer;
  logic [5:0] periph_data_atop,
              periph_data_buf_atop;

  logic [4:0]      perf_counters;
  logic            clk_int;

  // clock gate of the core_region less the core itself
  cluster_clock_gating clock_gate_i (
    .clk_i     ( clk_i       ),
    .en_i      ( clock_en_i  ),
    .test_en_i ( test_mode_i ),
    .clk_o     ( clk_int     )
  );


  logic [31:0] hart_id;
  always_comb begin
    hart_id = '0;
    hart_id[3:0] = CORE_ID[3:0];
    hart_id[10:5] = cluster_id_i;
  end
  logic [5:0] irq_ack_id;
  assign irq_ack_id_o = irq_ack_id[4:0];
  assert property (@(posedge clk_i) irq_ack_o |-> !irq_ack_id[5]);
  riscv_core #(
    .N_EXT_PERF_COUNTERS ( 5                 ),
    .FPU                 ( FPU               ),
    .SHARED_FP           ( SHARED_FP         ),
    .SHARED_DSP_MULT     ( SHARED_DSP_MULT   ),
    .SHARED_INT_DIV      ( SHARED_INT_DIV    ),
    .SHARED_FP_DIVSQRT   ( SHARED_FP_DIVSQRT ),
    .WAPUTYPE            ( WAPUTYPE          ),
    .PULP_HWLP           ( 1                 ),
    .N_PMP_ENTRIES       ( N_PMP_ENTRIES     )
  ) RISCV_CORE (
    .clk_i                 ( clk_i                    ),
    .rst_ni                ( rst_ni                   ),

    .clock_en_i            ( clock_en_i               ),
    .scan_cg_en_i          ( test_mode_i              ),

    .boot_addr_i           ( boot_addr_i              ),
    .dm_halt_addr_i        ( '0                       ),
    .hart_id_i             ( hart_id                  ),

    .instr_req_o           ( instr_req_o              ),
    .instr_gnt_i           ( instr_gnt_i              ),
    .instr_rvalid_i        ( instr_r_valid_i          ),
    .instr_addr_o          ( instr_addr_o             ),
    .instr_rdata_i         ( instr_r_rdata_i          ),

    .data_req_o            ( s_core_bus.req           ),
    .data_gnt_i            ( s_core_bus.gnt           ),
    .data_rvalid_i         ( s_core_bus.r_valid       ),
    .data_we_o             ( s_core_bus.we            ),
    .data_be_o             ( s_core_bus.be            ),
    .data_addr_o           ( s_core_bus.add           ),
    .data_wdata_o          ( s_core_bus.wdata         ),
    .data_rdata_i          ( s_core_bus.r_rdata       ),

    .data_atop_o           ( s_core_bus.atop          ),
    .data_buffer_o         ( core_buffer              ),
    .data_unaligned_o      ( unaligned_o              ),

    // apu-interconnect
    // handshake signals
    .apu_master_req_o      ( /* unused */             ),
    .apu_master_ready_o    ( /* unused */             ),
    .apu_master_gnt_i      ( '0                       ),
     // request channel
    .apu_master_operands_o ( /* unused */             ),
    .apu_master_op_o       ( /* unused */             ),
    .apu_master_type_o     ( /* unused */             ),
    .apu_master_flags_o    ( /* unused */             ),
    // response channel
    .apu_master_valid_i    ( '0                       ),
    .apu_master_result_i   ( '0                       ),
    .apu_master_flags_i    ( '0                       ),

    .irq_ack_o             ( irq_ack_o                ),
    .irq_id_o              ( irq_ack_id               ),

    .irq_software_i        ( '0                       ),
    .irq_timer_i           ( '0                       ),
    .irq_external_i        ( '0                       ),
    .irq_fast_i            ( '0                       ),

    .debug_req_i           ( debug_bus.req            ),

    .fetch_enable_i        ( fetch_en_i               ),
    .core_busy_o           ( core_busy_o              ),

    .pmp_conf_override_i   ( pmp_conf_override_i      ),
    .pmp_cfg_i             ( pmp_cfg_i                ),
    .pmp_addr_i            ( pmp_addr_i               )
  );

  assign debug_bus.r_opc = 1'b0;

  // Bind to 0 Unused Signals in CORE interface
  assign s_core_bus.r_gnt       = 1'b0;
  assign s_core_bus.barrier     = 1'b0;
  assign s_core_bus.exec_cancel = 1'b0;
  assign s_core_bus.exec_stall  = 1'b0;

  // Performance Counters
  assign perf_counters[4] = tcdm_data_master.req & (~tcdm_data_master.gnt);  // Cycles lost due to contention

  // demuxes to TCDM & memory hierarchy
  core_demux #(
    .ADDR_WIDTH             ( 32                      ),
    .DATA_WIDTH             ( 32                      ),
    .BYTE_ENABLE_BIT        ( DATA_WIDTH/8            ),
    .CLUSTER_ALIAS          ( CLUSTER_ALIAS           ),
    .CLUSTER_ALIAS_BASE     ( CLUSTER_ALIAS_BASE      ),
    .DEM_PER_BEFORE_TCDM_TS ( DEM_PER_BEFORE_TCDM_TS  ),
    .REMAP_ADDRESS          ( REMAP_ADDRESS           )
  ) core_demux_i (
    .clk                (  clk_int                    ),
    .rst_ni             (  rst_ni                     ),
    .test_en_i          (  test_mode_i                ),
    .base_addr_i        (  base_addr_i                ),

    .data_req_i         (  s_core_bus.req             ),
    .data_add_i         (  s_core_bus.add             ),
    .data_wen_i         ( ~s_core_bus.we              ), //inverted when using OR10N
    .data_atop_i        (  s_core_bus.atop            ),
    .data_wdata_i       (  s_core_bus.wdata           ),
    .data_be_i          (  s_core_bus.be              ),
    .data_gnt_o         (  s_core_bus.gnt             ),
    .data_r_gnt_i       (  s_core_bus.r_gnt           ),
    .data_r_valid_o     (  s_core_bus.r_valid         ),
    .data_r_opc_o       (                             ),
    .data_r_rdata_o     (  s_core_bus.r_rdata         ),

    .data_req_o_SH      (  tcdm_data_master.req       ),
    .data_add_o_SH      (  tcdm_data_master.add       ),
    .data_wen_o_SH      (  tcdm_data_master.wen       ),
    .data_atop_o_SH     (  tcdm_data_master_atop      ),
    .data_wdata_o_SH    (  tcdm_data_master.wdata     ),
    .data_be_o_SH       (  tcdm_data_master.be        ),
    .data_gnt_i_SH      (  tcdm_data_master.gnt       ),
    .data_r_valid_i_SH  (  tcdm_data_master.r_valid   ),
    .data_r_rdata_i_SH  (  tcdm_data_master.r_rdata   ),

    .data_req_o_EXT     (  periph_demux_bus.req       ),
    .data_add_o_EXT     (  periph_demux_bus.add       ),
    .data_wen_o_EXT     (  periph_demux_bus.wen       ),
    .data_wdata_o_EXT   (  periph_demux_bus.wdata     ),
    .data_be_o_EXT      (  periph_demux_bus.be        ),
    .data_gnt_i_EXT     (  periph_demux_bus.gnt       ),
    .data_r_valid_i_EXT (  periph_demux_bus.r_valid   ),
    .data_r_rdata_i_EXT (  periph_demux_bus.r_rdata   ),
    .data_r_opc_i_EXT   (  periph_demux_bus.r_opc     ),

    .data_req_o_PE      (  periph_data.req            ),
    .data_add_o_PE      (  periph_data.add            ),
    .data_wen_o_PE      (  periph_data.wen            ),
    .data_atop_o_PE     (  periph_data_atop           ),
    .data_wdata_o_PE    (  periph_data.wdata          ),
    .data_be_o_PE       (  periph_data.be             ),
    .data_gnt_i_PE      (  periph_data.gnt            ),
    .data_r_valid_i_PE  (  periph_data.r_valid        ),
    .data_r_rdata_i_PE  (  periph_data.r_rdata        ),
    .data_r_opc_i_PE    (  periph_data.r_opc          ),

    .perf_l2_ld_o       (  perf_counters[0]           ),
    .perf_l2_st_o       (  perf_counters[1]           ),
    .perf_l2_ld_cyc_o   (  perf_counters[2]           ),
    .perf_l2_st_cyc_o   (  perf_counters[3]           ),
    .CLUSTER_ID         (  cluster_id_i               )
  );


  generate
    if(USE_STORE_BUFFER == 1'b1) begin : store_buffer_gen
      riscv_store_buffer #(
        .Depth      (16),
        .AddrWidth  (32),
        .DataWidth  (32)
      ) i_store_buf (
        .clk_i    ( clk_int   ),
        .rst_ni,
        // Upstream
        .addr_i       ( periph_data.add         ),
        .we_ni        ( periph_data.wen         ),
        .buffer_i     ( core_buffer             ),
        .be_i         ( periph_data.be          ),
        .wdata_i      ( periph_data.wdata       ),
        .atop_i       ( periph_data_atop        ),
        .req_i        ( periph_data.req         ),
        .gnt_o        ( periph_data.gnt         ),
        .rdata_o      ( periph_data.r_rdata     ),
        .rvalid_o     ( periph_data.r_valid     ),
        // Downstream
        .addr_o       ( periph_data_buf.add     ),
        .we_no        ( periph_data_buf.wen     ),
        .be_o         ( periph_data_buf.be      ),
        .wdata_o      ( periph_data_buf.wdata   ),
        .atop_o       ( periph_data_buf_atop    ),
        .req_o        ( periph_data_buf.req     ),
        .gnt_i        ( periph_data_buf.gnt     ),
        .rdata_i      ( periph_data_buf.r_rdata ),
        .rvalid_i     ( periph_data_buf.r_valid )
      );
      assign periph_data.r_id  =   '0;
      assign periph_data.r_opc = 1'b0;
      assign periph_data_buf.id = periph_data.id;
    end
    else begin: no_store_buffer_gen
      assign periph_data_buf.add = periph_data.add;
      assign periph_data_buf.wen = periph_data.wen;
      assign periph_data_buf.be = periph_data.be;
      assign periph_data_buf.wdata = periph_data.wdata;
      assign periph_data_buf_atop = periph_data_atop;
      assign periph_data_buf.req = periph_data.req;
      assign periph_data.gnt = periph_data_buf.gnt;
      assign periph_data.r_rdata = periph_data_buf.r_rdata;
      assign periph_data.r_valid = periph_data_buf.r_valid;
      assign periph_data.r_id = '0;
      assign periph_data.r_opc = 1'b0;
      assign periph_data_buf.id = periph_data.id;
    end
  endgenerate  

  periph_demux #(
    .DEM_PER_BEFORE_TCDM_TS (DEM_PER_BEFORE_TCDM_TS)
  ) periph_demux_i (
    .clk               ( clk_int                  ),
    .rst_ni            ( rst_ni                   ),

    .data_req_i        ( periph_demux_bus.req     ),
    .data_add_i        ( periph_demux_bus.add     ),
    .data_wen_i        ( periph_demux_bus.wen     ),
    .data_wdata_i      ( periph_demux_bus.wdata   ),
    .data_be_i         ( periph_demux_bus.be      ),
    .data_gnt_o        ( periph_demux_bus.gnt     ),

    .data_r_valid_o    ( periph_demux_bus.r_valid ),
    .data_r_opc_o      ( periph_demux_bus.r_opc   ),
    .data_r_rdata_o    ( periph_demux_bus.r_rdata ),

    .data_req_o_MH     ( dma_ctrl_master.req      ),
    .data_add_o_MH     ( dma_ctrl_master.add      ),
    .data_wen_o_MH     ( dma_ctrl_master.wen      ),
    .data_wdata_o_MH   ( dma_ctrl_master.wdata    ),
    .data_be_o_MH      ( dma_ctrl_master.be       ),
    .data_gnt_i_MH     ( dma_ctrl_master.gnt      ),

    .data_r_valid_i_MH ( dma_ctrl_master.r_valid  ),
    .data_r_rdata_i_MH ( dma_ctrl_master.r_rdata  ),
    .data_r_opc_i_MH   ( dma_ctrl_master.r_opc    ),

    .data_req_o_EU     ( eu_ctrl_master.req       ),
    .data_add_o_EU     ( eu_ctrl_master.add       ),
    .data_wen_o_EU     ( eu_ctrl_master.wen       ),
    .data_wdata_o_EU   ( eu_ctrl_master.wdata     ),
    .data_be_o_EU      ( eu_ctrl_master.be        ),
    .data_gnt_i_EU     ( eu_ctrl_master.gnt       ),

    .data_r_valid_i_EU ( eu_ctrl_master.r_valid   ),
    .data_r_rdata_i_EU ( eu_ctrl_master.r_rdata   ),
    .data_r_opc_i_EU   ( eu_ctrl_master.r_opc     ),

    .data_req_o_MYF    ( this_fifo.req            ),
    .data_add_o_MYF    ( this_fifo.add            ),
    .data_wen_o_MYF    ( this_fifo.wen            ),
    .data_wdata_o_MYF  ( this_fifo.wdata          ),
    .data_be_o_MYF     ( this_fifo.be             ),
    .data_gnt_i_MYF    ( this_fifo.gnt            ),

    .data_r_valid_i_MYF( this_fifo.r_valid        ),
    .data_r_rdata_i_MYF( this_fifo.r_rdata        ),
    .data_r_opc_i_MYF  ( this_fifo.r_opc          ),

    .data_req_o_NBF    ( next_fifo_master.req     ),
    .data_add_o_NBF    ( next_fifo_master.add     ),
    .data_wen_o_NBF    ( next_fifo_master.wen     ),
    .data_wdata_o_NBF  ( next_fifo_master.wdata   ),
    .data_be_o_NBF     ( next_fifo_master.be      ),
    .data_gnt_i_NBF    ( next_fifo_master.gnt     ),

    .data_r_valid_i_NBF( next_fifo_master.r_valid ),
    .data_r_rdata_i_NBF( next_fifo_master.r_rdata ),
    .data_r_opc_i_NBF  ( next_fifo_master.r_opc   ),

    .data_req_o_HDRV    ( hpu_driver_master.req ),
    .data_add_o_HDRV    ( hpu_driver_master.add ),
    .data_wen_o_HDRV    ( hpu_driver_master.wen ),
    .data_wdata_o_HDRV  ( hpu_driver_master.wdata),
    .data_be_o_HDRV     ( hpu_driver_master.be  ),
    .data_gnt_i_HDRV    ( hpu_driver_master.gnt ),

    .data_r_valid_i_HDRV( hpu_driver_master.r_valid ),
    .data_r_rdata_i_HDRV( hpu_driver_master.r_rdata ),
    .data_r_opc_i_HDRV  ( hpu_driver_master.r_opc   )


  );

  if (INTER_CORE_FIFO_DEPTH > 0) begin : gen_inter_core_fifo
    inter_core_fifo #(
      .Depth  (INTER_CORE_FIFO_DEPTH)
    ) i_inter_core_fifo (
      .clk_i,
      .rst_ni,
      .push_slv (this_fifo_slave),
      .pop_slv  (this_fifo)
    );
  end else begin : gen_no_inter_core_fifo
    assign this_fifo_slave.gnt = 1'b1;
    assign this_fifo_slave.r_valid = 1'b1;
    assign this_fifo_slave.r_rdata = '0;
    assign this_fifo_slave.r_opc = '0;
    assign this_fifo.gnt = 1'b1;
    assign this_fifo.r_valid = 1'b1;
    assign this_fifo.r_rdata = '0;
    assign this_fifo.r_opc = '0;
  end

  virtual_stdout_demux #(
    .CoreId (CORE_ID)
  ) i_stdout (
    .clk_i              (clk_int),
    .rst_ni,
    .cluster_id_i,
    .periph_slv         (periph_data_buf),
    .periph_slv_atop_i  (periph_data_buf_atop),
    .periph_mst         (periph_data_master),
    .periph_mst_atop_o  (periph_data_master_atop)
  );

  /* debug stuff */
  //synopsys translate_off

  // COMPARE THE output of the instruction CACHE with the slm files generated by the compiler
`ifdef DEBUG_FETCH_INTERFACE
  integer FILE;
  string  FILENAME;
  string  FILE_ID;

  logic                         instr_gnt_L2;
  logic                         instr_gnt_ROM;
  logic [INSTR_RDATA_WIDTH-1:0] instr_r_rdata_ROM;
  logic                         instr_r_valid_ROM;
  logic [INSTR_RDATA_WIDTH-1:0] instr_r_rdata_L2;
  logic                         instr_r_valid_L2;
  logic                         destination; //--> 0 fetch from BOOT_ROM, 1--> fetch from L2_MEMORY

  initial
  begin
    FILE_ID.itoa(CORE_ID);
    FILENAME = {"FETCH_CORE_", FILE_ID, ".log" };
    FILE=$fopen(FILENAME,"w");
  end

  // BOOT code is loaded in this dummy ROM_MEMORY
/* -----\/----- EXCLUDED -----\/-----
  generate
    case(INSTR_RDATA_WIDTH)
      128: begin
        ibus_lint_memory_128 #(
          .addr_width    ( 16           ),
          .INIT_MEM_FILE ( ROM_SLM_FILE )
        ) ROM_MEMORY (
          .clk            ( clk_i              ),
          .rst_n          ( rst_ni             ),
          .lint_req_i     ( instr_req_o        ),
          .lint_grant_o   ( instr_gnt_ROM      ),
          .lint_addr_i    ( instr_addr_o[19:4] ), //instr_addr_o[17:2]   --> 2^17 bytes max program
          .lint_r_rdata_o ( instr_r_rdata_ROM  ),
          .lint_r_valid_o ( instr_r_valid_ROM  )
        );

        // application code is loaded in this dummy L2_MEMORY
        ibus_lint_memory_128 #(
          .addr_width    ( 16          ),
          .INIT_MEM_FILE ( L2_SLM_FILE )
        ) L2_MEMORY (
          .clk            ( clk_i              ),
          .rst_n          ( rst_ni             ),
          .lint_req_i     ( instr_req_o        ),
          .lint_grant_o   ( instr_gnt_L2       ),
          .lint_addr_i    ( instr_addr_o[19:4] ), //instr_addr_o[17:2]    --> 2^17 bytes max program
          .lint_r_rdata_o ( instr_r_rdata_L2   ),
          .lint_r_valid_o ( instr_r_valid_L2   )
        );
      end
      32: begin
        ibus_lint_memory #(
          .addr_width      ( 16              ),
          .INIT_MEM_FILE   ( ROM_SLM_FILE    )
        ) ROM_MEMORY (
          .clk             ( clk_i              ),
          .rst_n           ( rst_ni             ),
          .lint_req_i      ( instr_req_o        ),
          .lint_grant_o    ( instr_gnt_ROM      ),
          .lint_addr_i     ( instr_addr_o[17:2] ), //instr_addr_o[17:2]   --> 2^17 bytes max program
          .lint_r_rdata_o  ( instr_r_rdata_ROM  ),
          .lint_r_valid_o  ( instr_r_valid_ROM  )
        );

        // application code is loaded in this dummy L2_MEMORY
        ibus_lint_memory #(
          .addr_width      ( 16                 ),
          .INIT_MEM_FILE   ( L2_SLM_FILE        )
        ) L2_MEMORY (
          .clk             ( clk_i              ),
          .rst_n           ( rst_ni             ),
          .lint_req_i      ( instr_req_o        ),
          .lint_grant_o    ( instr_gnt_L2       ),
          .lint_addr_i     ( instr_addr_o[17:2] ), //instr_addr_o[17:2]    --> 2^17 bytes max program
          .lint_r_rdata_o  ( instr_r_rdata_L2   ),
          .lint_r_valid_o  ( instr_r_valid_L2   )
        );
      end
    endcase // INSTR_RDATA_WIDTH
  endgenerate
 -----/\----- EXCLUDED -----/\----- */

  // SELF CHECK ROUTINES TO compare isntruction fetches with slm files
  always_ff @(posedge clk_i)
  begin
    if(instr_r_valid_i) begin
      $fwrite( FILE , "\t --> %8h\n",instr_r_rdata_i);
      case(destination)
        1'b1: begin
          // Not active by default as it is wrong once the code is dynamically modified
          //if(instr_r_rdata_i !== instr_r_rdata_L2)
          //begin
          //  $warning("Error DURING L2 fetch: %x != %x", instr_r_rdata_i, instr_r_rdata_L2);
          //  $stop();
          //end
        end
        1'b0: begin
          if(instr_r_rdata_i !== instr_r_rdata_ROM) begin
            $warning("Error DURING ROM Fetch: %x != %x", instr_r_rdata_i, instr_r_rdata_ROM);
            $stop();
          end
        end
      endcase
    end
    //DUMP TO FILE every transaction to instruction cache
    if(instr_req_o & instr_gnt_i) begin
      if(instr_addr_o[31:24] == 8'h1A)
        destination <= 1'b0;
      else
        destination <= 1'b1;
`ifdef DUMP_INSTR_FETCH
      $fwrite( FILE , "%t [ns]: FETCH at address %8h",$time/1000, instr_addr_o);
`endif
    end
  end
`endif

`ifdef DATA_MISS
  logic data_hit;
  logic req;
`endif
  logic reg_cache_refill;

  always_ff @(posedge clk_i , negedge rst_ni)
  begin
    if ( rst_ni == 1'b0 ) begin
      reg_cache_refill <= 1'b0;
    end
    else begin
      if (instr_req_o)
        reg_cache_refill <= 1'b1;
      else if(instr_r_valid_i && !instr_req_o)
        reg_cache_refill <= 1'b0;
    end
  end
//synopsys translate_on

/* verilator tracing_off */

endmodule
