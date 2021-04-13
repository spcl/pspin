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

import pspin_cfg_pkg::*;

module soc_dma_wrap #(
    /// id width of the DMA AXI Master port
    parameter int unsigned DmaAxiIdWidth      = -1,
    /// data width of the DMA AXI Master port
    parameter int unsigned DmaDataWidth       = -1,
    /// user width
    parameter int unsigned DmaUserWidth       = -1,
    /// number of AX requests in-flight
    parameter int unsigned AxiAxReqDepth      = -1,
    /// number of 1D transfers buffered in backend
    parameter int unsigned TfReqFifoDepth     = -1,
    /// NHI data request type
    parameter type axi_nhi_req_t              = logic,
    /// NHI data response type
    parameter type axi_nhi_res_t              = logic,
    /// host data request type (64 bit)
    parameter type axi_host_req_t             = logic,
    /// host data response type (64 bit)
    parameter type axi_host_res_t             = logic
) (
    input  logic             clk_i,
    input  logic             rst_ni,

    //command
    input  logic             cmd_req_valid_i,
    output logic             cmd_req_ready_o,
    input  pspin_cmd_t       cmd_req_i,

    //response
    output logic             cmd_resp_valid_o,
    output pspin_cmd_resp_t  cmd_resp_o,

    /// to NHI (32 bit address)
    output axi_nhi_req_t     nhi_req_o,
    input  axi_nhi_res_t     nhi_resp_i,

    /// to host (64 bit address)
    output axi_host_req_t    host_req_o,
    input  axi_host_res_t    host_resp_i
);

  localparam logic[64:0] PCIeStartAddr  = 65'h1_0000_0000_0000_0000;
  localparam logic[64:0] PCIeEndAddr    = 65'h1_FFFF_FFFF_FFFF_FFFF;
  localparam logic[64:0] NHIStartAddr   = 65'h0_0000_0000_0000_0000;
  localparam logic[64:0] NHIEndAddr     = 65'h0_0000_0000_FFFF_FFFF;

  localparam int unsigned IDX_PCIE = 0;
  localparam int unsigned IDX_NHI  = 1;
  localparam int unsigned RespFIFODepth = TfReqFifoDepth + AxiAxReqDepth;

  localparam int unsigned DmaAddrWidth = 65; //64th bit used to distinguish host/NIC addresses

  logic [$clog2(RespFIFODepth):0] to_pop_rx_d;
  logic [$clog2(RespFIFODepth):0] to_pop_rx_q;

  logic [$clog2(RespFIFODepth):0] to_pop_tx_d;
  logic [$clog2(RespFIFODepth):0] to_pop_tx_q;

  logic tx_req_valid, rx_req_valid;
  logic tx_req_ready, rx_req_ready;
  logic tx_resp_valid, rx_resp_valid;

  transf_descr_soc_t xfer_descr;
  pspin_cmd_resp_t cmd_resp;

  pspin_cmd_resp_t cmd_rx_resp, cmd_tx_resp;

  logic fifo_rx_full, fifo_tx_full;
  logic fifo_rx_sel, fifo_tx_sel;

  logic fifo_rx_pop, fifo_tx_pop;

  logic fifo_rx_resp_avail, fifo_tx_resp_avail;

  assign xfer_descr.num_bytes         = cmd_req_i.descr.host_dma_cmd.length;
  
  assign xfer_descr.dst_addr[64]      = (cmd_req_i.descr.host_dma_cmd.nic_to_host) ? 1'b1 : 1'b0;
  assign xfer_descr.dst_addr[63:32]   = (cmd_req_i.descr.host_dma_cmd.nic_to_host) ? cmd_req_i.descr.host_dma_cmd.host_addr[63:32] : '0;
  assign xfer_descr.dst_addr[31:0]    = (cmd_req_i.descr.host_dma_cmd.nic_to_host) ? cmd_req_i.descr.host_dma_cmd.host_addr[31:0]  : cmd_req_i.descr.host_dma_cmd.nic_addr;
  
  assign xfer_descr.src_addr[64]      = (cmd_req_i.descr.host_dma_cmd.nic_to_host) ? 1'b0 : 1'b1;
  assign xfer_descr.src_addr[63:32]   = (cmd_req_i.descr.host_dma_cmd.nic_to_host) ? '0 : cmd_req_i.descr.host_dma_cmd.host_addr[63:32];
  assign xfer_descr.src_addr[31:0]    = (cmd_req_i.descr.host_dma_cmd.nic_to_host) ? cmd_req_i.descr.host_dma_cmd.nic_addr : cmd_req_i.descr.host_dma_cmd.host_addr[31:0];
  assign xfer_descr.deburst           = 1'b0;
  assign xfer_descr.decouple          = 1'b1;
  assign xfer_descr.serialize         = 1'b0; // TODO: connect me!

  assign cmd_resp.cmd_id              = cmd_req_i.cmd_id;

  always_comb begin
      cmd_req_ready_o = 1'b0;
      rx_req_valid = 1'b0;
      tx_req_valid = 1'b0;

      if (cmd_req_valid_i) begin
        cmd_req_ready_o = (cmd_req_i.descr.host_dma_cmd.nic_to_host) ? (!fifo_rx_full && rx_req_ready) : (!fifo_tx_full && tx_req_ready);
        rx_req_valid    = cmd_req_i.descr.host_dma_cmd.nic_to_host == 1'b1;
        tx_req_valid    = cmd_req_i.descr.host_dma_cmd.nic_to_host == 1'b0;
      end
  end

  //FIFO with RX responses
  assign fifo_rx_resp_avail = to_pop_rx_q > 0;
  assign fifo_rx_pop = fifo_rx_resp_avail && fifo_rx_sel;

  fifo_v3 #(
    .dtype     (pspin_cmd_resp_t),
    .DEPTH     (RespFIFODepth)
  ) i_rx_resp_fifo (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .flush_i   (1'b0),
    .testmode_i(1'b0),
    .full_o    (fifo_rx_full),
    .empty_o   (),
    .usage_o   (),
    .data_i    (cmd_resp),
    .push_i    (cmd_req_ready_o && rx_req_valid),
    .data_o    (cmd_rx_resp),
    .pop_i     (fifo_rx_pop)
  );

  always_comb begin
    case ({rx_resp_valid, fifo_rx_pop})
        2'b10   : to_pop_rx_d = to_pop_rx_q + 1;
        2'b01   : to_pop_rx_d = to_pop_rx_q - 1;
        default : to_pop_rx_d = to_pop_rx_q;
    endcase
  end

  //FIFO with TX responses
  assign fifo_tx_resp_avail = to_pop_tx_q > 0;
  assign fifo_tx_pop = fifo_tx_resp_avail && fifo_tx_sel;

  fifo_v3 #(
    .dtype     (pspin_cmd_resp_t),
    .DEPTH     (RespFIFODepth)
  ) i_tx_resp_fifo (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .flush_i   (1'b0),
    .testmode_i(1'b0),
    .full_o    (fifo_tx_full),
    .empty_o   (),
    .usage_o   (),
    .data_i    (cmd_resp),
    .push_i    (cmd_req_ready_o && tx_req_valid),
    .data_o    (cmd_tx_resp),
    .pop_i     (fifo_tx_pop)
  );

  always_comb begin
    case ({tx_resp_valid, fifo_tx_pop})
        2'b10   : to_pop_tx_d = to_pop_tx_q + 1;
        2'b01   : to_pop_tx_d = to_pop_tx_q - 1;
        default : to_pop_tx_d = to_pop_tx_q;
    endcase
  end

  // arbitrate response from the two ports
  rr_arb_tree #(
    .NumIn      (2),
    .DataType   (pspin_cmd_resp_t),
    .ExtPrio    (0),
    .AxiVldRdy  (1),
    .LockIn     (1)
  ) i_resp_arb (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .flush_i    (1'b0),
    .rr_i       ('0),
    .req_i      ({fifo_tx_resp_avail, fifo_rx_resp_avail}),
    .gnt_o      ({fifo_tx_sel, fifo_rx_sel}),
    .data_i     ({cmd_tx_resp, cmd_rx_resp}),
    .gnt_i      (1'b1),
    .req_o      (cmd_resp_valid_o),
    .data_o     (cmd_resp_o),
    .idx_o      ()
  );

  typedef logic [DmaDataWidth-1    :0] data_t;
  typedef logic [DmaAxiIdWidth-1   :0] id_t;
  typedef logic [DmaDataWidth/8-1  :0] strb_t;
  typedef logic [DmaUserWidth-1    :0] user_t;
  typedef logic [DmaAddrWidth-1    :0] wide_addr_t;


  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, wide_addr_t, id_t, user_t);
  `AXI_TYPEDEF_W_CHAN_T (w_chan_t, data_t, strb_t, user_t);
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, wide_addr_t, id_t, user_t);
  `AXI_TYPEDEF_B_CHAN_T (b_chan_t, id_t, user_t);
  `AXI_TYPEDEF_R_CHAN_T (r_chan_t, data_t, id_t, user_t);
  `AXI_TYPEDEF_REQ_T    (axi_dma_wide_req_t, aw_chan_t, w_chan_t, ar_chan_t);
  `AXI_TYPEDEF_RESP_T   (axi_dma_wide_resp_t, b_chan_t, r_chan_t);

  axi_dma_wide_req_t  nhi_wide_req;
  axi_dma_wide_req_t  host_wide_req;

  //cut NHI address to 32 bit (lower)
  assign nhi_req_o.aw.id     = nhi_wide_req.aw.id;
  assign nhi_req_o.aw.addr   = nhi_wide_req.aw.addr[31:0];
  assign nhi_req_o.aw.len    = nhi_wide_req.aw.len;
  assign nhi_req_o.aw.size   = nhi_wide_req.aw.size;
  assign nhi_req_o.aw.burst  = nhi_wide_req.aw.burst;
  assign nhi_req_o.aw.lock   = nhi_wide_req.aw.lock;
  assign nhi_req_o.aw.cache  = nhi_wide_req.aw.cache;
  assign nhi_req_o.aw.prot   = nhi_wide_req.aw.prot;
  assign nhi_req_o.aw.qos    = nhi_wide_req.aw.qos;
  assign nhi_req_o.aw.region = nhi_wide_req.aw.region;
  assign nhi_req_o.aw.atop   = nhi_wide_req.aw.atop;
  assign nhi_req_o.aw.user   = nhi_wide_req.aw.user;
  assign nhi_req_o.aw_valid  = nhi_wide_req.aw_valid;

  assign nhi_req_o.w.data     = nhi_wide_req.w.data;
  assign nhi_req_o.w.strb     = nhi_wide_req.w.strb;
  assign nhi_req_o.w.last     = nhi_wide_req.w.last;
  assign nhi_req_o.w.user     = nhi_wide_req.w.user;
  assign nhi_req_o.w_valid    = nhi_wide_req.w_valid;

  assign nhi_req_o.ar.id      = nhi_wide_req.ar.id;
  assign nhi_req_o.ar.addr    = nhi_wide_req.ar.addr[31:0];
  assign nhi_req_o.ar.len     = nhi_wide_req.ar.len;
  assign nhi_req_o.ar.size    = nhi_wide_req.ar.size;
  assign nhi_req_o.ar.burst   = nhi_wide_req.ar.burst;
  assign nhi_req_o.ar.lock    = nhi_wide_req.ar.lock;
  assign nhi_req_o.ar.cache   = nhi_wide_req.ar.cache;
  assign nhi_req_o.ar.prot    = nhi_wide_req.ar.prot;
  assign nhi_req_o.ar.qos     = nhi_wide_req.ar.qos;
  assign nhi_req_o.ar.region  = nhi_wide_req.ar.region;
  assign nhi_req_o.ar.user    = nhi_wide_req.ar.user;
  assign nhi_req_o.ar_valid   = nhi_wide_req.ar_valid;

  assign nhi_req_o.r_ready    = nhi_wide_req.r_ready;
  assign nhi_req_o.b_ready    = nhi_wide_req.b_ready;

  //cut host address to 64 bit (lower)
  assign host_req_o.aw.id     = host_wide_req.aw.id;
  assign host_req_o.aw.addr   = host_wide_req.aw.addr[63:0];
  assign host_req_o.aw.len    = host_wide_req.aw.len;
  assign host_req_o.aw.size   = host_wide_req.aw.size;
  assign host_req_o.aw.burst  = host_wide_req.aw.burst;
  assign host_req_o.aw.lock   = host_wide_req.aw.lock;
  assign host_req_o.aw.cache  = host_wide_req.aw.cache;
  assign host_req_o.aw.prot   = host_wide_req.aw.prot;
  assign host_req_o.aw.qos    = host_wide_req.aw.qos;
  assign host_req_o.aw.region = host_wide_req.aw.region;
  assign host_req_o.aw.atop   = host_wide_req.aw.atop;
  assign host_req_o.aw.user   = host_wide_req.aw.user;
  assign host_req_o.aw_valid  = host_wide_req.aw_valid;

  assign host_req_o.w.data    = host_wide_req.w.data;
  assign host_req_o.w.strb    = host_wide_req.w.strb;
  assign host_req_o.w.last    = host_wide_req.w.last;
  assign host_req_o.w.user    = host_wide_req.w.user;
  assign host_req_o.w_valid   = host_wide_req.w_valid;

  assign host_req_o.ar.id     = host_wide_req.ar.id;
  assign host_req_o.ar.addr   = host_wide_req.ar.addr[63:0];
  assign host_req_o.ar.len    = host_wide_req.ar.len;
  assign host_req_o.ar.size   = host_wide_req.ar.size;
  assign host_req_o.ar.burst  = host_wide_req.ar.burst;
  assign host_req_o.ar.lock   = host_wide_req.ar.lock;
  assign host_req_o.ar.cache  = host_wide_req.ar.cache;
  assign host_req_o.ar.prot   = host_wide_req.ar.prot;
  assign host_req_o.ar.qos    = host_wide_req.ar.qos;
  assign host_req_o.ar.region = host_wide_req.ar.region;
  assign host_req_o.ar.user   = host_wide_req.ar.user;
  assign host_req_o.ar_valid  = host_wide_req.ar_valid;

  assign host_req_o.r_ready   = host_wide_req.r_ready;
  assign host_req_o.b_ready   = host_wide_req.b_ready;

  //DMA engine
  pspin_soc_dma #(
    .DmaAxiIdWidth  (DmaAxiIdWidth),
    .DmaDataWidth   (DmaDataWidth),
    .DmaAddrWidth   (DmaAddrWidth),
    .DmaUserWidth   (DmaUserWidth),
    .AxiAxReqDepth  (AxiAxReqDepth),
    .TfReqFifoDepth (TfReqFifoDepth),
    .axi_req_t      (axi_dma_wide_req_t),
    .axi_res_t      (axi_dma_wide_resp_t),
    .transf_descr_t (pspin_cfg_pkg::transf_descr_soc_t),
    .PCIeStartAddr  (PCIeStartAddr),
    .PCIeEndAddr    (PCIeEndAddr),
    .NHIStartAddr   (NHIStartAddr),
    .NHIEndAddr     (NHIEndAddr)
  ) i_soc_dma (
    .clk_i          (clk_i              ),
    .rst_ni         (rst_ni             ),
    //direct hw port 1
    .rx_req_valid_i (rx_req_valid       ),
    .rx_req_ready_o (rx_req_ready       ),
    .rx_req_i       (xfer_descr         ),
    .rx_rsp_valid_o (rx_resp_valid      ),
    //direct hw port 2
    .tx_req_valid_i (tx_req_valid       ),
    .tx_req_ready_o (tx_req_ready       ),
    .tx_req_i       (xfer_descr         ),
    .tx_rsp_valid_o (tx_resp_valid      ),
    //AXI wide port 1 (to NHI)
    .nhi_dma_req_o  (nhi_wide_req       ),
    .nhi_dma_res_i  (nhi_resp_i         ),
    //AXI wide port 2 (to HOST)
    .pcie_dma_req_o (host_wide_req      ),
    .pcie_dma_res_i (host_resp_i        ),
    //status
    .idle_o         (                   )
  );

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      to_pop_tx_q <= '0;
      to_pop_rx_q <= '0;
    end else begin
      to_pop_tx_q <= to_pop_tx_d;
      to_pop_rx_q <= to_pop_rx_d;
    end
  end

endmodule