// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module virtual_stdout_demux #(
  parameter int unsigned CoreId = 0
) (
  input  logic            clk_i,
  input  logic            rst_ni,
  input  logic [5:0]      cluster_id_i,
  XBAR_PERIPH_BUS.Slave   periph_slv,
  input  logic [5:0]      periph_slv_atop_i,
  XBAR_PERIPH_BUS.Master  periph_mst,
  output logic [5:0]      periph_mst_atop_o
);

  `ifndef TARGET_SYNTHESIS
    `define VIRTUAL_STDOUT 
  `endif
  
  `ifndef VIRTUAL_STDOUT
    // When synthesizing, feed signals through to real stdout device.
    assign periph_mst.req     = periph_slv.req;
    assign periph_mst.add     = periph_slv.add;
    assign periph_mst.wen     = periph_slv.wen;
    assign periph_mst_atop_o  = periph_slv_atop_i;
    assign periph_mst.wdata   = periph_slv.wdata;
    assign periph_mst.be      = periph_slv.be;
    assign periph_slv.gnt     = periph_mst.gnt;
    assign periph_slv.r_valid = periph_mst.r_valid;
    assign periph_slv.r_rdata = periph_mst.r_rdata;
    assign periph_slv.r_opc   = periph_mst.r_opc;
  `else
    // When not synthesizing, insert virtual stdout device that is close to the core for fast and
    // interference-free printing.

    byte buffer [$];

    function void flush();
      automatic string s;
      for (int i_char = 0; i_char < buffer.size(); i_char++) begin
        s = $sformatf("%s%c", s, buffer[i_char]);
      end
      if (s.len() > 0) begin
        $display("[%01d,%01d] %s", cluster_id_i, CoreId, s);
      end
      buffer.delete();
    endfunction

    function void append(byte ch);
      if (ch == 8'hA) begin
        flush();
      end else begin
        buffer.push_back(ch);
      end
    endfunction

    logic resp_inj_d, resp_inj_q;
    always_comb begin
      // Feed through by default.
      periph_mst.req     = periph_slv.req;
      periph_mst.add     = periph_slv.add;
      periph_mst.wen     = periph_slv.wen;
      periph_mst_atop_o  = periph_slv_atop_i;
      periph_mst.wdata   = periph_slv.wdata;
      periph_mst.be      = periph_slv.be;
      periph_slv.gnt     = periph_mst.gnt;
      periph_slv.r_valid = periph_mst.r_valid;
      periph_slv.r_rdata = periph_mst.r_rdata;
      periph_slv.r_opc   = periph_mst.r_opc;
      resp_inj_d = resp_inj_q;
      // Inject responses by stdout device.
      if (resp_inj_q) begin
        periph_slv.r_valid = 1'b1;
        periph_slv.r_rdata = '0;
        periph_slv.r_opc = 1'b0;
        resp_inj_d = 1'b0;
      end
      // Intercept accesses to stdout device.
      if (periph_slv.req && periph_slv.add[31:12] == 20'h1A104) begin
        periph_mst.req = 1'b0;
        periph_slv.gnt = 1'b1;
        resp_inj_d = 1'b1;
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        flush();
        resp_inj_q <= 1'b0;
      end else begin
        resp_inj_q <= resp_inj_d;
        if (resp_inj_d) begin
          append(periph_slv.wdata & 32'hFF);
        end
      end
    end
  `endif

endmodule
