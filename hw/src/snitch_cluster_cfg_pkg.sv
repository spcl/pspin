`include "axi/assign.svh"
`include "axi/typedef.svh"

package snitch_cluster_cfg_pkg;

  localparam int unsigned NrCores = pspin_cfg_pkg::NUM_CORES;
  localparam int unsigned NrHives = 1;

  localparam int unsigned AddrWidth = pspin_cfg_pkg::AXI_SOC_AW;
  localparam int unsigned NarrowDataWidth = pspin_cfg_pkg::AXI_NARROW_DW;
  localparam int unsigned WideDataWidth = pspin_cfg_pkg::AXI_WIDE_DW;

  localparam int unsigned NarrowIdWidthIn = pspin_cfg_pkg::AXI_IW;
  localparam int unsigned NrMasters = 3 + NrHives;
  localparam int unsigned NarrowIdWidthOut = $clog2(NrMasters) + NarrowIdWidthIn;

  localparam int unsigned NrDmaMasters = 2; // ??
  localparam int unsigned WideIdWidthIn = 6; // ?
  localparam int unsigned WideIdWidthOut = $clog2(NrDmaMasters) + WideIdWidthIn;

  localparam int unsigned UserWidth = pspin_cfg_pkg::AXI_UW;

  localparam int unsigned ICacheLineWidth [NrHives] = '{ 128 };
  localparam int unsigned ICacheLineCount [NrHives] = '{ 1024 };
  localparam int unsigned ICacheSets [NrHives] = '{ 4 };

  localparam int unsigned PhysicalAddrWidth = pspin_cfg_pkg::AXI_SOC_AW;
  localparam int unsigned BootAddr = 32'h1e000000;

  localparam int unsigned TCDMDepth = 4096;
  localparam int unsigned TCDMBanks = 64;

  localparam int unsigned DMAAxiReqFifoDepth = 3;
  localparam int unsigned DMAReqFifoDepth = 3;

  localparam int unsigned RVE     = 8'b00000000;
  localparam int unsigned RVF     = 8'b11111111;
  localparam int unsigned RVD     = 8'b11111111;
  localparam int unsigned XF16    = 8'b00000000;
  localparam int unsigned XF16ALT = 8'b00000000;
  localparam int unsigned XF8     = 8'b00000000;
  localparam int unsigned XFVEC   = 8'b00000000;
  localparam int unsigned Xdma    = 8'b00000000;
  localparam int unsigned Xssr    = 8'b11111111;
  localparam int unsigned Xfrep   = 8'b11111111;

  localparam int unsigned NumSsrsMax = 3;

  localparam int unsigned NumIntOutstandingLoads [NrCores] = '{1, 1, 1, 1, 1, 1, 1, 1};
  localparam int unsigned NumIntOutstandingMem [NrCores] = '{4, 4, 4, 4, 4, 4, 4, 4};
  localparam int unsigned NumFPOutstandingLoads [NrCores] = '{4, 4, 4, 4, 4, 4, 4, 4};
  localparam int unsigned NumFPOutstandingMem [NrCores] = '{4, 4, 4, 4, 4, 4, 4, 4};
  localparam int unsigned NumDTLBEntries [NrCores] = '{1, 1, 1, 1, 1, 1, 1, 1};
  localparam int unsigned NumITLBEntries [NrCores] = '{1, 1, 1, 1, 1, 1, 1, 1};
  localparam int unsigned NumSequencerInstr [NrCores] = '{16, 16, 16, 16, 16, 16, 16, 16};
  localparam int unsigned NumSsrs [NrCores] = '{3, 3, 3, 3, 3, 3, 3, 3};
  localparam int unsigned SsrMuxRespDepth [NrCores] = '{4, 4, 4, 4, 4, 4, 4, 4};

  localparam int unsigned Hive [NrCores] = '{0, 0, 0, 0, 0, 0, 0, 0};

  localparam int unsigned Radix = 2;
  localparam int unsigned RegisterOffloadReq = 1;
  localparam int unsigned RegisterOffloadRsp = 1;
  localparam int unsigned RegisterCoreReq = 1;
  localparam int unsigned RegisterCoreRsp = 1;
  localparam int unsigned RegisterTCDMCuts = 0;
  localparam int unsigned RegisterExtWide = 0;
  localparam int unsigned RegisterExtNarrow = 0;
  localparam int unsigned RegisterFPUReq = 0;
  localparam int unsigned RegisterSequencer = 0;
  localparam int unsigned IsoCrossing = 0;

  typedef logic [AddrWidth-1:0]         addr_t;
  typedef logic [NarrowDataWidth-1:0]   data_t;
  typedef logic [NarrowDataWidth/8-1:0] strb_t;
  typedef logic [WideDataWidth-1:0]     data_dma_t;
  typedef logic [WideDataWidth/8-1:0]   strb_dma_t;
  typedef logic [NarrowIdWidthIn-1:0]   narrow_in_id_t;
  typedef logic [NarrowIdWidthOut-1:0]  narrow_out_id_t;
  typedef logic [WideIdWidthIn-1:0]     wide_in_id_t;
  typedef logic [WideIdWidthOut-1:0]    wide_out_id_t;
  typedef logic [UserWidth-1:0]         user_t;

  `AXI_TYPEDEF_ALL(narrow_in, addr_t, narrow_in_id_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_ALL(narrow_out, addr_t, narrow_out_id_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_ALL(wide_in, addr_t, wide_in_id_t, data_dma_t, strb_dma_t, user_t)
  `AXI_TYPEDEF_ALL(wide_out, addr_t, wide_out_id_t, data_dma_t, strb_dma_t, user_t)
  
  
  localparam snitch_pma_pkg::snitch_pma_t SnitchPMACfg = '{
      NrCachedRegionRules: 1,
      CachedRegion: '{
          '{base: 32'h1e000000, mask: 32'h800000}
      },

      NrExecuteRegionRules: 1,
      ExecuteRegion: '{
          '{base: 32'h1e000000, mask: 32'h800000}
      },
      default: 0
  };

  localparam fpnew_pkg::fpu_implementation_t FPUImplementation = '{
        PipeRegs: // FMA Block
                  '{
                    '{  3, // FP32
                        3, // FP64
                        1, // FP16
                        1, // FP8
                        2  // FP16alt
                      },
                    '{default: 1},   // DIVSQRT
                    '{default: 1},   // NONCOMP
                    '{default: 1}},   // CONV
        UnitTypes: '{'{default: fpnew_pkg::MERGED},
                    '{default: fpnew_pkg::DISABLED}, // DIVSQRT
                    '{default: fpnew_pkg::PARALLEL}, // NONCOMP
                    '{default: fpnew_pkg::MERGED}},  // CONV
        PipeConfig: fpnew_pkg::BEFORE
  };

  localparam snitch_ssr_pkg::ssr_cfg_t [3-1:0] SsrCfgs [NrCores] = '{
    '{'{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3}},
    '{'{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3}},
    '{'{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3}},
    '{'{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3}},
    '{'{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3}},
    '{'{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3}},
    '{'{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3}},
    '{'{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3},
      '{0, 1, 4, 16, 18, 3, 4, 3, 4, 3}}
  };

  localparam logic [3-1:0][4:0] SsrRegs [NrCores] = '{
    '{2, 1, 0},
    '{2, 1, 0},
    '{2, 1, 0},
    '{2, 1, 0},
    '{2, 1, 0},
    '{2, 1, 0},
    '{2, 1, 0},
    '{2, 1, 0}
  };

endpackage
// verilog_lint: waive-stop package-filename