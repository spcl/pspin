// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "common_cells/registers.svh"

module l2_mem #(
  parameter int unsigned  AXI_AW = 0,   // [bit], must be a power of 2
  parameter int unsigned  AXI_DW = 0,   // [bit], must be a power of 2
  parameter int unsigned  AXI_IW = 0,   // [bit]
  parameter int unsigned  AXI_UW = 0,   // [bit]
  // Memory
  parameter int unsigned  N_BYTES = 0,   // [B], must be a power of 2
  // Cuts
  parameter int unsigned  CUT_DW = 64,  // [bit], must be a power of 2 and >=8
  parameter int unsigned  CUT_N_WORDS = 16384,  // must be a power of 2
  parameter int unsigned  N_PAR_CUTS = AXI_DW / CUT_DW
) (
  input  logic  clk_i,
  input  logic  rst_ni,
  AXI_BUS.Slave slv_a,
  AXI_BUS.Slave slv_b
);

  // Properties of one memory cut, keep synchronized with instantiated macro.
  //localparam int unsigned CUT_DW = 64;          // [bit], must be a power of 2 and >=8
  //localparam int unsigned CUT_N_WORDS = 16384;  // must be a power of 2
  localparam int unsigned CUT_N_BITS = CUT_DW * CUT_N_WORDS;

  // Derived properties of memory array
  //localparam int unsigned N_PAR_CUTS = N_PAR_CUTS_MUL * AXI_DW / CUT_DW;
  localparam int unsigned PAR_CUTS_N_BYTES = N_PAR_CUTS * CUT_N_BITS / 8;
  localparam int unsigned N_SER_CUTS = N_BYTES / PAR_CUTS_N_BYTES;

  localparam int unsigned MEM_ADDR_WIDTH = $clog2(CUT_N_WORDS * N_SER_CUTS);
  typedef logic [N_PAR_CUTS-1:0][MEM_ADDR_WIDTH-1:0]  mem_addr_t;
  typedef logic [N_PAR_CUTS-1:0][CUT_DW-1:0]          mem_data_t;
  typedef logic [N_PAR_CUTS-1:0][CUT_DW/8-1:0]        mem_strb_t;
  typedef logic [N_PAR_CUTS-1:0]                      mem_logic_t;

  mem_logic_t             mem_req,
                          mem_wen;
  mem_addr_t              mem_addr;
  mem_data_t              mem_wdata,
                          mem_rdata;
  mem_strb_t              mem_be;

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW),
    .AXI_USER_WIDTH (AXI_UW)
  ) internal_a ();

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW),
    .AXI_USER_WIDTH (AXI_UW)
  ) internal_b ();

  axi_buf_intf #(
    .AW_DEPTH   (32'd2),
    .W_DEPTH    (32'd1),
    .ADDR_WIDTH (AXI_AW),
    .DATA_WIDTH (AXI_DW),
    .ID_WIDTH   (AXI_IW),
    .USER_WIDTH (AXI_UW)
  ) i_axi_a_buf (
    .clk_i,
    .rst_ni,
    .slv    (slv_a),
    .mst    (internal_a)
  );

  axi_buf_intf #(
    .AW_DEPTH   (32'd2),
    .W_DEPTH    (32'd1),
    .ADDR_WIDTH (AXI_AW),
    .DATA_WIDTH (AXI_DW),
    .ID_WIDTH   (AXI_IW),
    .USER_WIDTH (AXI_UW)
  ) i_axi_b_buf (
    .clk_i,
    .rst_ni,
    .slv    (slv_b),
    .mst    (internal_b)
  );

  axi_to_mem_banked_2p_intf #(
    .AXI_ID_WIDTH   (AXI_IW),
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_USER_WIDTH (AXI_UW),
    .MEM_NUM_BANKS  (N_PAR_CUTS),
    .MEM_ADDR_WIDTH (MEM_ADDR_WIDTH),
    .MEM_DATA_WIDTH (CUT_DW),
    .MEM_LATENCY    (1),
    .TOPOLOGY       (tcdm_interconnect_pkg::LIC)
  ) i_axi_to_mem_banked (
    .clk_i,
    .rst_ni,
    .test_i              (1'b0),
    .slv_a               (internal_a),
    .slv_b               (internal_b),
    .mem_req_o           (mem_req),
    .mem_gnt_i           ({N_PAR_CUTS{1'b1}}),
    .mem_add_o           (mem_addr),
    .mem_wen_o           (mem_wen),
    .mem_wdata_o         (mem_wdata),
    .mem_be_o            (mem_be),
    .mem_atop_o          (/* unused */),
    .mem_rdata_i         (mem_rdata),
    .axi_to_mem_busy_a_o (/* unused */),
    .axi_to_mem_busy_b_o (/* unused */)
  );

  // Interface from memory array to memory cuts
  localparam int unsigned WORD_IDX_OFF = 0; // output of `axi_to_mem_banked` is word-addressed
  localparam int unsigned WORD_IDX_WIDTH = $clog2(CUT_N_WORDS);
  localparam int unsigned ROW_IDX_OFF = WORD_IDX_OFF + WORD_IDX_WIDTH;
  localparam int unsigned ROW_IDX_WIDTH = $clog2(N_SER_CUTS);

  // Types for memory cuts
  typedef logic [$clog2(CUT_N_WORDS)-1:0] cut_addr_t;
  typedef logic [CUT_DW-1:0]              cut_data_t;

  logic       [N_PAR_CUTS-1:0][N_SER_CUTS-1:0]    cut_req;
  cut_addr_t  [N_PAR_CUTS-1:0]                    cut_addr_d, cut_addr_q;
  cut_data_t  [N_PAR_CUTS-1:0][N_SER_CUTS-1:0]    cut_rdata;
  logic       [N_PAR_CUTS-1:0][ROW_IDX_WIDTH-1:0] row_idx_d,  row_idx_q;

  for (genvar iCol = 0; iCol < N_PAR_CUTS; iCol++) begin : gen_cols
    assign cut_addr_d[iCol]
        = mem_req[iCol] ? mem_addr[iCol][WORD_IDX_OFF+:WORD_IDX_WIDTH] : cut_addr_q[iCol];

    if (ROW_IDX_WIDTH > 0) begin : gen_row_idx
      assign row_idx_d[iCol]
          = mem_req[iCol] ? mem_addr[iCol][ROW_IDX_OFF+:ROW_IDX_WIDTH] : row_idx_q[iCol];
      always_comb begin
        cut_req[iCol] = '0;
        cut_req[iCol][row_idx_d[iCol]] = mem_req[iCol];
      end
      assign mem_rdata[iCol] = cut_rdata[iCol][row_idx_q[iCol]];

    end else begin : gen_no_row_idx
      assign cut_req[iCol][0] = mem_req[iCol];
      assign mem_rdata[iCol] = cut_rdata[iCol][0];
    end

    for (genvar iRow = 0; iRow < N_SER_CUTS; iRow++) begin : gen_rows
      sram #(
        .DATA_WIDTH (CUT_DW),
        .N_WORDS    (CUT_N_WORDS)
      ) i_mem_cut (
        .clk_i,
        .rst_ni,
        .req_i    (cut_req[iCol][iRow]),
        .we_i     (mem_wen[iCol]),
        .addr_i   (cut_addr_d[iCol]),
        .wdata_i  (mem_wdata[iCol]),
        .be_i     (mem_be[iCol]),
        .rdata_o  (cut_rdata[iCol][iRow])
      );
    end
  end

  `FFARN(cut_addr_q, cut_addr_d, '0, clk_i, rst_ni)
  `FFARN(row_idx_q, row_idx_d, '0, clk_i, rst_ni)

  // Validate parameters and properties.
  // pragma translate_off
  initial begin
    assert (AXI_AW > 0);
    assert (AXI_AW % (2**$clog2(AXI_AW)) == 0);
    assert (AXI_DW > 0);
    assert (AXI_DW % (2**$clog2(AXI_DW)) == 0);
    assert (N_BYTES > 0);
    assert (N_BYTES % (2**$clog2(N_BYTES)) == 0);
    assert (CUT_DW % (2**$clog2(CUT_DW)) == 0);
    assert (CUT_DW >= 8);
    assert (AXI_DW >= CUT_DW);
    assert (CUT_N_WORDS % 2**$clog2(CUT_N_WORDS) == 0);
    assert (N_BYTES % PAR_CUTS_N_BYTES == 0);
    assert (N_PAR_CUTS >= AXI_DW/CUT_DW);
  end
  // pragma translate_on

endmodule
