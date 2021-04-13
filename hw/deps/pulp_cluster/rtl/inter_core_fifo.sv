// Copyright 2020 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "common_cells/registers.svh"

module inter_core_fifo #(
  parameter int unsigned Depth = 32'd0
) (
  input  logic                clk_i,
  input  logic                rst_ni,
  XBAR_PERIPH_BUS.Slave       push_slv,
  XBAR_PERIPH_BUS.Slave       pop_slv
);

  localparam int unsigned CntWidth = (Depth > 1) ? $clog2(Depth) : 1;
  localparam int unsigned DataWidth = 32;

  typedef logic  [CntWidth-1:0] cnt_t;
  typedef logic [DataWidth-1:0] data_t;

  cnt_t   usage;
  data_t  pop_data;
  logic   pop_rvalid_d,     pop_rvalid_q,
          push_rvalid_d,    push_rvalid_q,
          push_valid,
          push_ready,
          pop_valid,
          pop_ready;
  enum logic {Data, Usage}
          pop_rdata_src_d,  pop_rdata_src_q;

  stream_fifo #(
    .FALL_THROUGH (1'b0),
    .DEPTH        (Depth),
    .T            (data_t)
  ) i_fifo (
    .clk_i,
    .rst_ni,
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .data_i     (push_slv.wdata),
    .valid_i    (push_valid),
    .ready_o    (push_ready),
    .data_o     (pop_data),
    .valid_o    (pop_valid),
    .ready_i    (pop_ready),
    .usage_o    (usage)
  );

  // Handle push interface.
  assign push_slv.r_rdata = {{DataWidth-CntWidth{1'b0}}, usage};
  assign push_slv.r_opc = '0;
  assign push_slv.r_id = '0;
  assign push_slv.r_valid = push_rvalid_q;
  always_comb begin
    push_rvalid_d = 1'b0;
    push_slv.gnt  = 1'b0;
    push_valid    = 1'b0;
    if (push_slv.req) begin
      unique case ({push_slv.wen, push_slv.add[3:0]})
        {1'b0, 4'h0}: begin // write to push address
          push_valid = 1'b1;
          push_slv.gnt = push_ready;
          if (push_ready) begin
            push_rvalid_d = 1'b1;
          end
        end
        default: begin // all reads and other writes return the current fill count
          push_slv.gnt = 1'b1;
          push_rvalid_d = 1'b1;
        end
      endcase
    end
  end

  // Handle pop interface.
  assign pop_ready = pop_rvalid_q;
  assign pop_slv.r_valid = pop_rvalid_q;
  assign pop_slv.r_rdata = pop_rdata_src_q == Data ? pop_data : {{DataWidth-CntWidth{1'b0}}, usage};
  always_comb begin
    pop_rdata_src_d = Data;
    pop_rvalid_d    = 1'b0;
    pop_slv.gnt     = 1'b0;
    if (pop_slv.req) begin
      unique case ({pop_slv.wen, pop_slv.add[3:0]})
        {1'b1, 4'h0}: begin // read from pop address
          // Since the actual pop happens in the next cycle, we need to prevent an underrun by
          // accepting two consecutive pop requests if the current usage is 1.  So if the usage is
          // one, we require that we are not popping in the current cycle.
          if (pop_valid && (usage != 1 || !pop_ready)) begin
            pop_slv.gnt = 1'b1;
            pop_rvalid_d = 1'b1;
          end
        end
        default: begin // all writes and other reads return the current fill count
          pop_slv.gnt = 1'b1;
          pop_rdata_src_d = Usage;
          pop_rvalid_d = 1'b1;
        end
      endcase
    end
  end

  `FFARN(pop_rdata_src_q, pop_rdata_src_d, Data, clk_i, rst_ni)
  `FFARN(pop_rvalid_q, pop_rvalid_d, 1'b0, clk_i, rst_ni)
  `FFARN(push_rvalid_q, push_rvalid_d, 1'b0, clk_i, rst_ni)

endmodule
