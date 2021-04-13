// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "axi/typedef.svh"
`include "common_cells/registers.svh"

/// Program memory shared by all clusters, with an additional port for the host to deploy handler
/// code.
module prog_mem #(
  parameter int unsigned NumClusters = 0,
  parameter int unsigned NumBytes = 0,
  parameter int unsigned AddrWidth = 0,
  parameter int unsigned DataWidth = 0,
  parameter int unsigned IdWidth = 0,
  parameter int unsigned UserWidth = 0,
  parameter type req_t = logic,
  parameter type resp_t = logic
) (
  input  logic                    clk_i,
  input  logic                    rst_ni,

  input  req_t  [NumClusters-1:0] cl_req_i,
  output resp_t [NumClusters-1:0] cl_resp_o,
  input  req_t                    host_req_i,
  output resp_t                   host_resp_o
);

  // Types of input and output channels.
  typedef logic [AddrWidth-1:0]   addr_t;
  typedef logic [DataWidth-1:0]   data_t;
  typedef logic [IdWidth-1:0]     id_t;
  typedef logic [DataWidth/8-1:0] strb_t;
  typedef logic [UserWidth-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_t, data_t, id_t, user_t)

  // Slave ports of multiplexer.
  localparam int unsigned NumSlvPorts = NumClusters + 1;
  req_t  [NumSlvPorts-1:0]  req;
  resp_t [NumSlvPorts-1:0]  resp;
  for (genvar i = 0; i < NumSlvPorts; i++) begin : gen_bind_slv_ports
    if (i < NumClusters) begin : gen_bind_cluster
      assign req[i] = cl_req_i[i];
      assign cl_resp_o[i] = resp[i];
    end else begin : gen_bind_host
      assign req[i] = host_req_i;
      assign host_resp_o = resp[i];
    end
  end

  // Types of master ports of multiplexer.
  parameter int unsigned MuxIdWidth = IdWidth + cf_math_pkg::idx_width(NumSlvPorts);
  typedef logic [MuxIdWidth-1:0] mux_id_t;
  `AXI_TYPEDEF_AW_CHAN_T(mux_aw_t, addr_t, mux_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mux_b_t, mux_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mux_ar_t, addr_t, mux_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mux_r_t, data_t, mux_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(mux_req_t, mux_aw_t, w_t, mux_ar_t)
  `AXI_TYPEDEF_RESP_T(mux_resp_t, mux_b_t, mux_r_t)
  mux_req_t  mux_req;
  mux_resp_t mux_resp;
  // Instantiation of multiplexer.
  axi_mux #(
    .SlvAxiIDWidth  (IdWidth),
    .slv_aw_chan_t  (aw_t),
    .mst_aw_chan_t  (mux_aw_t),
    .w_chan_t       (w_t),
    .slv_b_chan_t   (b_t),
    .mst_b_chan_t   (mux_b_t),
    .slv_ar_chan_t  (ar_t),
    .mst_ar_chan_t  (mux_ar_t),
    .slv_r_chan_t   (r_t),
    .mst_r_chan_t   (mux_r_t),
    .slv_req_t      (req_t),
    .slv_resp_t     (resp_t),
    .mst_req_t      (mux_req_t),
    .mst_resp_t     (mux_resp_t),
    .NoSlvPorts     (NumSlvPorts),
    .MaxWTrans      (1),
    .FallThrough    (1'b0),
    .SpillAw        (1'b0),
    .SpillW         (1'b0),
    .SpillB         (1'b0),
    .SpillAr        (1'b0),
    .SpillR         (1'b0)
  ) i_mux (
    .clk_i,
    .rst_ni,
    .test_i       (1'b0),
    .slv_reqs_i   (req),
    .slv_resps_o  (resp),
    .mst_req_o    (mux_req),
    .mst_resp_i   (mux_resp)
  );

  // AXI-to-memory converter
  logic   mem_req,
          mem_req_q,
          mem_we;
  addr_t  axi_to_mem_addr;
  data_t  mem_rdata,
          mem_wdata;
  strb_t  mem_strb;
  axi_to_mem #(
    .axi_req_t  (mux_req_t),
    .axi_resp_t (mux_resp_t),
    .AddrWidth  (AddrWidth),
    .DataWidth  (DataWidth),
    .IdWidth    (MuxIdWidth),
    .NumBanks   (1),
    .BufDepth   (1)
  ) i_axi_to_mem (
    .clk_i,
    .rst_ni,
    .busy_o       (/* unused */),
    .axi_req_i    (mux_req),
    .axi_resp_o   (mux_resp),
    .mem_req_o    (mem_req),
    .mem_gnt_i    (1'b1),
    .mem_addr_o   (axi_to_mem_addr),
    .mem_wdata_o  (mem_wdata),
    .mem_strb_o   (mem_strb),
    .mem_atop_o   (/* unsupported */),
    .mem_we_o     (mem_we),
    .mem_rvalid_i (mem_req_q),
    .mem_rdata_i  (mem_rdata)
  );
  `FFARN(mem_req_q, mem_req, 1'b0, clk_i, rst_ni)

  // Truncation of addresses into SRAM
  localparam int unsigned NumWords = NumBytes / (DataWidth / 8);
  localparam int unsigned ByteOffset = $clog2(DataWidth / 8);
  localparam int unsigned MemAddrWidth = cf_math_pkg::idx_width(NumWords);
  typedef logic [MemAddrWidth-1:0] mem_addr_t;
  mem_addr_t mem_addr;
  assign mem_addr = axi_to_mem_addr[ByteOffset+:MemAddrWidth];

  // SRAM macro
  sram #(
    .DATA_WIDTH (DataWidth),
    .N_WORDS    (NumWords)
  ) i_sram (
    .clk_i,
    .rst_ni,
    .req_i    (mem_req),
    .we_i     (mem_we),
    .addr_i   (mem_addr),
    .wdata_i  (mem_wdata),
    .be_i     (mem_strb),
    .rdata_o  (mem_rdata)
  );

endmodule
