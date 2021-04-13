// Copyright 2020 ETH Zurich and University of Bologna.
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

module nhi_port_wrap
#(
  parameter DMA_AXI_AW_WIDTH   = 32,
  parameter DMA_AXI_DW_WIDTH   = 512,
  parameter DMA_AXI_ID_WIDTH   = 4,
  parameter DMA_AXI_UW_WIDTH   = 4
) (
  input logic                      clk_i,
  input logic                      rst_ni,

  WIDE_DMA_TCDM_BUS.Master         s_wide_dma_superbanks,
  AXI_BUS.Slave                    s_wide_dma_nhi
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
  axi_dma_req_t   axi_dma_tcdm_req;
  axi_dma_resp_t  axi_dma_tcdm_res;

  // connect to external AXI
  `AXI_ASSIGN_TO_REQ(axi_dma_tcdm_req, s_wide_dma_nhi);
  `AXI_ASSIGN_FROM_RESP (s_wide_dma_nhi, axi_dma_tcdm_res);

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
  ) i_axi_to_mem_nhi (
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

endmodule
