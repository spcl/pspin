// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "axi/typedef.svh"

module axi_buf #(
  parameter int unsigned  AwDepth       = 32'd0,
  parameter bit           AwFallthrough = 1'b1,
  parameter int unsigned  WDepth        = 32'd0,
  parameter bit           WFallthrough  = 1'b1,
  parameter int unsigned  BDepth        = 32'd0,
  parameter bit           BFallthrough  = 1'b1,
  parameter int unsigned  ArDepth       = 32'd0,
  parameter bit           ArFallthrough = 1'b1,
  parameter int unsigned  RDepth        = 32'd0,
  parameter bit           RFallthrough  = 1'b1,
  parameter type          req_t         = logic,
  parameter type          resp_t        = logic,
  parameter int unsigned  AddrWidth     = 32'd0,
  parameter int unsigned  DataWidth     = 32'd0,
  parameter int unsigned  IdWidth       = 32'd0,
  parameter int unsigned  UserWidth     = 32'd0
) (
  input  logic  clk_i,
  input  logic  rst_ni,

  input  req_t  slv_req_i,
  output resp_t slv_resp_o,

  output req_t  mst_req_o,
  input  resp_t mst_resp_i
);

  typedef logic [AddrWidth-1:0]   addr_t;
  typedef logic [DataWidth-1:0]   data_t;
  typedef logic [DataWidth/8-1:0] strb_t;
  typedef logic [IdWidth-1:0]     id_t;
  typedef logic [UserWidth-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)

  if (AwDepth == 0) begin : gen_no_aw_fifo
    assign mst_req_o.aw         = slv_req_i.aw;
    assign mst_req_o.aw_valid   = slv_req_i.aw_valid;
    assign slv_resp_o.aw_ready  = mst_resp_i.aw_ready;
  end else begin
    stream_fifo #(
      .FALL_THROUGH (AwFallthrough),
      .DATA_WIDTH   ($bits(aw_chan_t)),
      .DEPTH        (AwDepth)
    ) i_aw_fifo (
      .clk_i,
      .rst_ni,
      .flush_i    (1'b0),
      .testmode_i (1'b0),
      .usage_o    (/* unused */),
      .data_i     (slv_req_i.aw),
      .valid_i    (slv_req_i.aw_valid),
      .ready_o    (slv_resp_o.aw_ready),
      .data_o     (mst_req_o.aw),
      .valid_o    (mst_req_o.aw_valid),
      .ready_i    (mst_resp_i.aw_ready)
    );
  end

  if (WDepth == 0) begin : gen_no_w_fifo
    assign mst_req_o.w        = slv_req_i.w;
    assign mst_req_o.w_valid  = slv_req_i.w_valid;
    assign slv_resp_o.w_ready = mst_resp_i.w_ready;
  end else begin
    stream_fifo #(
      .FALL_THROUGH (WFallthrough),
      .DATA_WIDTH   ($bits(w_chan_t)),
      .DEPTH        (WDepth)
    ) i_w_fifo (
      .clk_i,
      .rst_ni,
      .flush_i    (1'b0),
      .testmode_i (1'b0),
      .usage_o    (/* unused */),
      .data_i     (slv_req_i.w),
      .valid_i    (slv_req_i.w_valid),
      .ready_o    (slv_resp_o.w_ready),
      .data_o     (mst_req_o.w),
      .valid_o    (mst_req_o.w_valid),
      .ready_i    (mst_resp_i.w_ready)
    );
  end

  if (BDepth == 0) begin : gen_no_b_fifo
    assign slv_resp_o.b       = mst_resp_i.b;
    assign slv_resp_o.b_valid = mst_resp_i.b_valid;
    assign mst_req_o.b_ready  = slv_req_i.b_ready;
  end else begin
    stream_fifo #(
      .FALL_THROUGH (BFallthrough),
      .DATA_WIDTH   ($bits(b_chan_t)),
      .DEPTH        (BDepth)
    ) i_b_fifo (
      .clk_i,
      .rst_ni,
      .flush_i    (1'b0),
      .testmode_i (1'b0),
      .usage_o    (/* unused */),
      .data_i     (mst_resp_i.b),
      .valid_i    (mst_resp_i.b_valid),
      .ready_o    (mst_req_o.b_ready),
      .data_o     (slv_resp_o.b),
      .valid_o    (slv_resp_o.b_valid),
      .ready_i    (slv_req_i.b_ready)
    );
  end

  if (ArDepth == 0) begin : gen_no_ar_fifo
    assign mst_req_o.ar         = slv_req_i.ar;
    assign mst_req_o.ar_valid   = slv_req_i.ar_valid;
    assign slv_resp_o.ar_ready  = mst_resp_i.ar_ready;
  end else begin
    stream_fifo #(
      .FALL_THROUGH (ArFallthrough),
      .DATA_WIDTH   ($bits(ar_chan_t)),
      .DEPTH        (ArDepth)
    ) i_ar_fifo (
      .clk_i,
      .rst_ni,
      .flush_i    (1'b0),
      .testmode_i (1'b0),
      .usage_o    (/* unused */),
      .data_i     (slv_req_i.ar),
      .valid_i    (slv_req_i.ar_valid),
      .ready_o    (slv_resp_o.ar_ready),
      .data_o     (mst_req_o.ar),
      .valid_o    (mst_req_o.ar_valid),
      .ready_i    (mst_resp_i.ar_ready)
    );
  end

  if (RDepth == 0) begin : gen_no_r_fifo
    assign slv_resp_o.r       = mst_resp_i.r;
    assign slv_resp_o.r_valid = mst_resp_i.r_valid;
    assign mst_req_o.r_ready  = slv_req_i.r_ready;
  end else begin
    stream_fifo #(
      .FALL_THROUGH (RFallthrough),
      .DATA_WIDTH   ($bits(r_chan_t)),
      .DEPTH        (RDepth)
    ) i_r_fifo (
      .clk_i,
      .rst_ni,
      .flush_i    (1'b0),
      .testmode_i (1'b0),
      .usage_o    (/* unused */),
      .data_i     (mst_resp_i.r),
      .valid_i    (mst_resp_i.r_valid),
      .ready_o    (mst_req_o.r_ready),
      .data_o     (slv_resp_o.r),
      .valid_o    (slv_resp_o.r_valid),
      .ready_i    (slv_req_i.r_ready)
    );
  end

endmodule

`include "axi/assign.svh"

module axi_buf_intf #(
  parameter int unsigned  AW_DEPTH        = 32'd0,
  parameter bit           AW_FALLTHROUGH  = 1'b1,
  parameter int unsigned  W_DEPTH         = 32'd0,
  parameter bit           W_FALLTHROUGH   = 1'b1,
  parameter int unsigned  B_DEPTH         = 32'd0,
  parameter bit           B_FALLTHROUGH   = 1'b1,
  parameter int unsigned  AR_DEPTH        = 32'd0,
  parameter bit           AR_FALLTHROUGH  = 1'b1,
  parameter int unsigned  R_DEPTH         = 32'd0,
  parameter bit           R_FALLTHROUGH   = 1'b1,
  parameter int unsigned  ADDR_WIDTH      = 32'd0,
  parameter int unsigned  DATA_WIDTH      = 32'd0,
  parameter int unsigned  ID_WIDTH        = 32'd0,
  parameter int unsigned  USER_WIDTH      = 32'd0
) (
  input  logic    clk_i,
  input  logic    rst_ni,
  AXI_BUS.Slave   slv,
  AXI_BUS.Master  mst
);

  typedef logic [ID_WIDTH-1:0]     id_t;
  typedef logic [ADDR_WIDTH-1:0]   addr_t;
  typedef logic [DATA_WIDTH-1:0]   data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;
  typedef logic [USER_WIDTH-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t  slv_req,  mst_req;
  resp_t slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)

  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_buf #(
    .AwDepth       (AW_DEPTH),
    .AwFallthrough (AW_FALLTHROUGH),
    .WDepth        (W_DEPTH),
    .WFallthrough  (W_FALLTHROUGH),
    .BDepth        (B_DEPTH),
    .BFallthrough  (B_FALLTHROUGH),
    .ArDepth       (AR_DEPTH),
    .ArFallthrough (AR_FALLTHROUGH),
    .RDepth        (R_DEPTH),
    .RFallthrough  (R_FALLTHROUGH),
    .req_t         (req_t),
    .resp_t        (resp_t),
    .AddrWidth     (ADDR_WIDTH),
    .DataWidth     (DATA_WIDTH),
    .IdWidth       (ID_WIDTH),
    .UserWidth     (USER_WIDTH)
  ) i_axi_buf (
    .clk_i,
    .rst_ni,
    .slv_req_i  (slv_req),
    .slv_resp_o (slv_resp),
    .mst_req_o  (mst_req),
    .mst_resp_i (mst_resp)
  );

endmodule
