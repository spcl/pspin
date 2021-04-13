// Copyright 2020 ETH Zurich and University of Bologna.
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

`include "common_cells/registers.svh"

module riscv_store_buffer #(
  // Maximum number of stores that can be outstanding.
  parameter int unsigned Depth = 0,
  parameter int unsigned AddrWidth = 0,
  parameter int unsigned DataWidth = 0,
  // Do not change the following constants.
  localparam type addr_t = logic [AddrWidth-1:0],
  localparam type atop_t = logic [5:0],
  localparam type data_t = logic [DataWidth-1:0],
  localparam type strb_t = logic [DataWidth/8-1:0]
) (
  input  logic  clk_i,
  input  logic  rst_ni,

  // Request Ports from RI5CY
  input  addr_t addr_i,
  input  logic  we_ni,
  input  logic  buffer_i,
  input  strb_t be_i,
  input  data_t wdata_i,
  input  atop_t atop_i,
  input  logic  req_i,
  output logic  gnt_o,
  // Response Ports to RI5CY
  output data_t rdata_o,
  output logic  rvalid_o,

  // Request Ports to Downstream
  output addr_t addr_o,
  output logic  we_no,
  output strb_t be_o,
  output data_t wdata_o,
  output atop_t atop_o,
  output logic  req_o,
  input  logic  gnt_i,
  // Response Ports from Downstream
  input  data_t rdata_i,
  input  logic  rvalid_i
);

  localparam int unsigned CntWidth = $clog2(Depth+1);

  typedef enum logic {Buffer, AwaitResp} state_t;
  typedef logic [CntWidth-1:0] cnt_t;

  cnt_t   cnt_d,    cnt_q;
  logic   rvalid_d, rvalid_q;
  state_t state_d,  state_q;

  // Feed non-handshake request signals through.
  assign addr_o       = addr_i;
  assign we_no        = we_ni;
  assign be_o         = be_i;
  assign wdata_o      = wdata_i;
  assign atop_o       = atop_i;

  function bit req_bufferable(logic we_n, logic buffer, atop_t atop);
    // Bufferable requests are non-atomic writes flagged as bufferable.
    return (!we_n && buffer && atop == '0);
  endfunction

  /*
  function automatic void fwd_and_complete(ref logic req_o, logic gnt_o, data_t rdata_o,
      logic rvalid_d, input logic gnt_i);
    // Forward the request and grant it as soon as downstream has granted it, ..
    req_o = 1'b1;
    gnt_o = gnt_i;
    // .. then report the write as complete.
    rdata_o = 32'hB4FFE3ED;
    rvalid_d = gnt_i;
  endfunction
  */

  function bit cnt_full(input cnt_t cnt_q);
    return (cnt_q == Depth);
  endfunction

  function bit cnt_empty(input cnt_t cnt_q);
    return (cnt_q == '0);
  endfunction

  /*
  function automatic void serve_req(
      input logic req_i, logic gnt_i, logic we_ni, logic buffer_i, atop_t atop_i, cnt_t cnt_q,
      ref logic req_o, logic gnt_o, data_t rdata_o, logic rvalid_d
  );
    if (req_i) begin
      if (req_bufferable(we_ni, buffer_i, atop_i)) begin
        if (!cnt_full(cnt_q)) begin
          fwd_and_complete(req_o, gnt_o, rdata_o, rvalid_d, gnt_i);
        end
      end else begin
        // Wait for counter to be empty.
        if (cnt_empty(cnt_q)) begin
          req_o = 1'b1;
          gnt_o = gnt_i;
          if (gnt_i) begin
            state_d = AwaitResp;
          end
        end
      end
    end
  endfunction
  */

  // Buffer Controller
  always_comb begin
    // Default assignments on core side.
    gnt_o = 1'b0;
    rdata_o = 'x;
    rvalid_d = 1'b0;
    rvalid_o = rvalid_q;
    // Default assignments on memory side.
    req_o = 1'b0;
    // Default state transition.
    state_d = state_q;
    // Handle requests.
    unique case (state_q)
      Buffer: begin
        //serve_req(req_i, gnt_i, we_ni, buffer_i, atop_i, cnt_q, req_o, gnt_o, rdata_o, rvalid_d);

        if (req_i) begin
            if (req_bufferable(we_ni, buffer_i, atop_i)) begin
                if (!cnt_full(cnt_q)) begin
                    // Forward the request and grant it as soon as downstream has granted it, ..
                    req_o = 1'b1;
                    gnt_o = gnt_i;
                    // .. then report the write as complete.
                    rdata_o = 32'hB4FFE3ED;
                    rvalid_d = gnt_i;
                end
            end else begin
                // Wait for counter to be empty.
                if (cnt_empty(cnt_q)) begin
                    req_o = 1'b1;
                    gnt_o = gnt_i;
                    if (gnt_i) begin
                        state_d = AwaitResp;
                    end
                end
            end
        end 
      end

      AwaitResp: begin
        rdata_o = rdata_i;
        rvalid_o = rvalid_i;
        if (rvalid_i) begin
          state_d = Buffer;
          // Serve next request.
          //serve_req(req_i, gnt_i, we_ni, buffer_i, atop_i, cnt_q, req_o, gnt_o, rdata_o, rvalid_d);

            if (req_i) begin
                if (req_bufferable(we_ni, buffer_i, atop_i)) begin
                    if (!cnt_full(cnt_q)) begin
                        // Forward the request and grant it as soon as downstream has granted it, ..
                        req_o = 1'b1;
                        gnt_o = gnt_i;
                        // .. then report the write as complete.
                        rdata_o = 32'hB4FFE3ED;
                        rvalid_d = gnt_i;
                    end
                end else begin
                    // Wait for counter to be empty.
                    if (cnt_empty(cnt_q)) begin
                        req_o = 1'b1;
                        gnt_o = gnt_i;
                        if (gnt_i) begin
                            state_d = AwaitResp;
                        end
                    end
                end
            end 
        end
      end

      default: /* do nothing */ ;
    endcase
  end

  // Count downstream transactions.
  always_comb begin
    cnt_d = cnt_q;
    if (req_o && gnt_i) begin
      cnt_d += 1;
    end
    if (rvalid_i) begin
      cnt_d -= 1;
    end
  end

  `FFARN(cnt_q, cnt_d, '0, clk_i, rst_ni)
  `FFARN(rvalid_q, rvalid_d, 1'b0, clk_i, rst_ni)
  `FFARN(state_q, state_d, Buffer, clk_i, rst_ni)

  `ifndef VERILATOR
  // Assertions
  default disable iff (!rst_ni);
  assert property (@(posedge clk_i)
      cnt_q == $past(cnt_q) || cnt_q == $past(cnt_q) + 1 || cnt_q == $past(cnt_q) - 1
  ) else $error("Counter over- or underflowed!");
  `endif

  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assert (AddrWidth > 0) else $fatal(1, "Address width must be non-zero!");
    assert (DataWidth > 0) else $fatal(1, "Data width must be non-zero!");
    assert (Depth     > 0) else $fatal(1, "Depth must be non-zero!");
  end
  `endif
  // pragma translate_on

endmodule
