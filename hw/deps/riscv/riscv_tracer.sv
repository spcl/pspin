// Copyright (c) 2019-2020 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Additional contributions by:                                               //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Salvatore Di Girolamo - digirols@inf.ethz.ch               //
//                                                                            //
// Design Name:    RISC-V Tracer                                              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Traces the executed instructions                           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import riscv_defines::*;
import riscv_tracer_defines::*;

// Source/Destination register instruction index
`define REG_S1 19:15
`define REG_S2 24:20
`define REG_S3 29:25
`define REG_S4 31:27
`define REG_D  11:07

module riscv_tracer (
  // Clock and Reset
  input  logic        clk,
  input  logic        rst_n,

  input  logic        fetch_enable,
  input  logic [31:0] hart_id_i,

  input  logic [31:0] pc,
  input  logic [31:0] instr,
  input  ctrl_state_e controller_state_i,

  input  logic        compressed,
  input  logic        id_valid,
  input  logic        is_decoding,
  input  logic        pipe_flush,
  input  logic        mret,
  input  logic        uret,
  input  logic        dret,
  input  logic        ecall,
  input  logic        ebreak,
  input  logic        fence,

  input  logic [31:0] rs1_value,
  input  logic [31:0] rs2_value,
  input  logic [31:0] rs3_value,

  input  logic [31:0] rs2_value_vec,

  input  logic        rd_is_fp,
  input  logic        rs1_is_fp,
  input  logic        rs2_is_fp,
  input  logic        rs3_is_fp,

  input  logic        ex_valid,
  input  logic [ 5:0] ex_reg_addr,
  input  logic        ex_reg_we,
  input  logic [31:0] ex_reg_wdata,

  input  logic        ex_data_req,
  input  logic        ex_data_gnt,
  input  logic        ex_data_we,
  input  logic [31:0] ex_data_addr,
  input  logic [31:0] ex_data_wdata,
  input  logic        data_misaligned,

  input  logic        wb_bypass,

  input  logic        wb_valid,
  input  logic [ 5:0] wb_reg_addr,
  input  logic        wb_reg_we,
  input  logic [31:0] wb_reg_wdata,

  input  logic [31:0] imm_u_type,
  input  logic [31:0] imm_uj_type,
  input  logic [31:0] imm_i_type,
  input  logic [11:0] imm_iz_type,
  input  logic [31:0] imm_z_type,
  input  logic [31:0] imm_s_type,
  input  logic [31:0] imm_sb_type,
  input  logic [31:0] imm_s2_type,
  input  logic [31:0] imm_s3_type,
  input  logic [31:0] imm_vs_type,
  input  logic [31:0] imm_vu_type,
  input  logic [31:0] imm_shuffle_type,
  input  logic [ 4:0] imm_clip_type
);

  `define ADDREG(REQ_QUEUE, R, ADDR, VAL) R.addr = ADDR; R.value = VAL; REQ_QUEUE.push_back(R);

  typedef enum logic [1:0] {Init, Running} state_t;

  typedef struct packed {
    logic [ 5:0] addr;
    logic [31:0] value;
  } reg_t;

  typedef struct packed {
    logic [31:0] addr;
    logic        we;
    logic [ 3:0] be;
    logic [31:0] wdata;
    logic [31:0] rdata;
  } mem_acc_t;

  class instr_trace_t;
    time         simtime;
    integer      cycles;
    logic [31:0] pc;
    logic [31:0] instr;
    reg_t        regs_read[$];
    reg_t        regs_write[$];
    mem_acc_t    mem_access[$];
    logic        run_ex;
    string       str;

    function new();
      str = "";
    endfunction

  endclass

  integer      f;
  string       fn;
  integer      cycles;
  logic [5:0]  rd, rs1, rs2, rs3, rs4;

  state_t       state;

  // TODO: this is super ugly but verilator currently does not 
  // support complex data types as function argurments. :-(
  instr_trace_t current_instr;

  instr_trace_t instr_ex[$];
  instr_trace_t instr_wb[$];
  instr_trace_t instr_ex_misaligned[$];
  instr_trace_t to_print[$];

  assign rd  = {rd_is_fp,  instr[`REG_D]};
  assign rs1 = {rs1_is_fp, instr[`REG_S1]};
  assign rs2 = {rs2_is_fp, instr[`REG_S2]};
  assign rs3 = {rs3_is_fp, instr[`REG_S3]};
  assign rs4 = {rs3_is_fp, instr[`REG_S4]};

  function void printMnemonic(input string mnemonic);
    begin
      current_instr.str = mnemonic;
    end
  endfunction // printMnemonic
  
  function void printRInstr(input string mnemonic);
    reg_t r;
    begin    
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF); 
      current_instr.str = $sformatf("%-16s x%0d, x%0d, x%0d", mnemonic, rd, rs1, rs2);
    end
  endfunction // printRInstr
  
  function void printAddNInstr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str = $sformatf("%-16s x%0d, x%0d, x%0d, 0x%0d", mnemonic, rd, rs1, rs2, $unsigned(imm_s3_type[4:0]));
    end
  endfunction // printAddNInstr

  function void printR1Instr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str = $sformatf("%-16s x%0d, x%0d", mnemonic, rd, rs1);
    end
  endfunction // printR1Instr

  function void printR3Instr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rd, rs3_value);
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str = $sformatf("%-16s x%0d, x%0d, x%0d", mnemonic, rd, rs1, rs2);
    end
  endfunction // printR3Instr

  function void printF3Instr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
      `ADDREG(current_instr.regs_read, r, rs4, rs3_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str = $sformatf("%-16s f%0d, f%0d, f%0d, f%0d", mnemonic, rd-32, rs1-32, rs2-32, rs4-32);
    end
  endfunction // printF3Instr

  function void printF2Instr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str = $sformatf("%-16s f%0d, f%0d, f%0d", mnemonic, rd-32, rs1-32, rs2-32);
    end
  endfunction // printF2Instr

  function void printF2IInstr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str = $sformatf("%-16s x%0d, f%0d, f%0d", mnemonic, rd, rs1-32, rs2-32);
    end
  endfunction // printF2IInstr

  function void printFInstr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str = $sformatf("%-16s f%0d, f%0d", mnemonic, rd-32, rs1-32);
    end
  endfunction // printFInstr

  function void printFIInstr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str = $sformatf("%-16s x%0d, f%0d", mnemonic, rd, rs1-32);
    end
  endfunction // printFIInstr

  function void printIFInstr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str = $sformatf("%-16s f%0d, x%0d", mnemonic, rd-32, rs1);
    end
  endfunction // printIFInstr

  function void printClipInstr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str = $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rd, rs1, $unsigned(imm_clip_type));
    end
  endfunction // printClipInstr

  function void printIInstr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str = $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rd, rs1, $signed(imm_i_type));
    end
  endfunction // printIInstr

  function void printIuInstr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str = $sformatf("%-16s x%0d, x%0d, 0x%0x", mnemonic, rd, rs1, imm_i_type);
    end
  endfunction // printIuInstr

  function void printUInstr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str = $sformatf("%-16s x%0d, 0x%0h", mnemonic, rd, {imm_u_type[31:12], 12'h000});
    end
  endfunction // printUInstr

  function void printUJInstr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str =  $sformatf("%-16s x%0d, %0d", mnemonic, rd, $signed(imm_uj_type));
    end
  endfunction // printUJInstr

  function void printSBInstr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
      current_instr.str = $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rs1, rs2, $signed(imm_sb_type));
    end
  endfunction // printSBInstr

  function void printSBallInstr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      current_instr.str =  $sformatf("%-16s x%0d, %0d", mnemonic, rs1, $signed(imm_sb_type));
    end
  endfunction // printSBallInstr

  function void printCSRInstr(input string mnemonic);
    logic [11:0] csr;
    reg_t r;
    begin
      csr = instr[31:20];

      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);

      if (instr[14] == 1'b0) begin
        `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
        current_instr.str = $sformatf("%-16s x%0d, x%0d, 0x%h", mnemonic, rd, rs1, csr);
      end else begin
        current_instr.str = $sformatf("%-16s x%0d, 0x%h, 0x%h", mnemonic, rd, imm_z_type, csr);
      end
    end
  endfunction // printCSRInstr

  function void printBit1Instr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str =  $sformatf("%-16s x%0d, x%0d, %0d, %0d", mnemonic, rd, rs1, imm_s3_type, imm_s2_type);
    end
  endfunction // printBit1Instr

  function void printBitRevInstr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str =  $sformatf("%-16s x%0d, x%0d, %0d, %0d", mnemonic, rd, rs1, imm_s2_type, imm_s3_type);
    end
  endfunction // printBitRevInstr

  function void printBit2Instr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rd, rs3_value);
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      current_instr.str =  $sformatf("%-16s x%0d, x%0d, %0d, %0d", mnemonic, rd, rs1, imm_s3_type, imm_s2_type);
    end
  endfunction // printBit2Instr

  function void printAtomicInstr(input string mnemonic);
    reg_t r;
    begin
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);
      if (instr[31:27] == AMO_LR) begin
        // Do not print rs2 for load-reserved
        current_instr.str = $sformatf("%-16s x%0d, (x%0d)", mnemonic, rd, rs1);
      end else begin
        current_instr.str = $sformatf("%-16s x%0d, x%0d, (x%0d)", mnemonic, rd, rs2, rs1);
      end
    end
  endfunction // printAtomicInstr

  function void printStoreBuffInstr();
    string mnemonic;
    reg_t r;
    begin

      case (instr[13:12])
        2'b00:  mnemonic = "bsb";
        2'b01:  mnemonic = "bsh";
        2'b10:  mnemonic = "bsw";
        2'b11: begin
          printMnemonic("INVALID");
          return;
        end
      endcase

      if (instr[14] == 1'b0) begin
        // regular store
        if (instr[6:0] != OPCODE_STORE_POST_BUF) begin
          `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
          `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
          current_instr.str = $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, rs2, $signed(imm_s_type), rs1);
        end else begin
          `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
          `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
          `ADDREG(current_instr.regs_write, r, rs1, 32'hDEADBEEF);
          current_instr.str = $sformatf("p.%-14s x%0d, %0d(x%0d!)", mnemonic, rs2, $signed(imm_s_type), rs1);
        end
      end else begin
        // reg-reg store
        if (instr[6:0] != OPCODE_STORE_POST_BUF) begin
          `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
          `ADDREG(current_instr.regs_read, r, rs3, rs3_value);
          `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
          current_instr.str = $sformatf("p.%-14s x%0d, x%0d(x%0d)", mnemonic, rs2, rs3, rs1);
        end else begin
          `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
          `ADDREG(current_instr.regs_read, r, rs3, rs3_value);
          `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
          `ADDREG(current_instr.regs_write, r, rs1, 32'hDEADBEEF);
          current_instr.str = $sformatf("p.%-14s x%0d, x%0d(x%0d!)", mnemonic, rs2, rs3, rs1);
        end
      end
    end
  endfunction // printStoreBuffInstr

  function void printStoreInstr();
    string mnemonic;
    reg_t r;
    begin

      case (instr[13:12])
        2'b00:  mnemonic = "sb";
        2'b01:  mnemonic = "sh";
        2'b10:  mnemonic = "sw";
        2'b11: begin
          printMnemonic("INVALID");
          return;
        end
      endcase

      if (instr[14] == 1'b0) begin
        // regular store
        if (instr[6:0] != OPCODE_STORE_POST) begin
          `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
          `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
          current_instr.str = $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, rs2, $signed(imm_s_type), rs1);
        end else begin
          `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
          `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
          `ADDREG(current_instr.regs_write, r, rs1, 32'hDEADBEEF);
          current_instr.str = $sformatf("p.%-14s x%0d, %0d(x%0d!)", mnemonic, rs2, $signed(imm_s_type), rs1);
        end
      end else begin
        // reg-reg store
        if (instr[6:0] != OPCODE_STORE_POST) begin
          `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
          `ADDREG(current_instr.regs_read, r, rs3, rs3_value);
          `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
          current_instr.str = $sformatf("p.%-14s x%0d, x%0d(x%0d)", mnemonic, rs2, rs3, rs1);
        end else begin
          `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
          `ADDREG(current_instr.regs_read, r, rs3, rs3_value);
          `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
          `ADDREG(current_instr.regs_write, r, rs1, 32'hDEADBEEF);
          current_instr.str = $sformatf("p.%-14s x%0d, x%0d(x%0d!)", mnemonic, rs2, rs3, rs1);
        end
      end
    end
  endfunction // printStoreInstr

  function void printHwloopInstr();
    string mnemonic;
    reg_t r;
    begin
      // set mnemonic
      case (instr[14:12])
        3'b000: mnemonic = "lp.starti";
        3'b001: mnemonic = "lp.endi";
        3'b010: mnemonic = "lp.count";
        3'b011: mnemonic = "lp.counti";
        3'b100: mnemonic = "lp.setup";
        3'b101: mnemonic = "lp.setupi";
        3'b111: begin
          printMnemonic("INVALID");
          return;
        end
      endcase

      // decode and print instruction
      case (instr[14:12])
        // lp.starti and lp.endi
        3'b000,
        3'b001: current_instr.str = $sformatf("%-16s 0x%0d, 0x%0h", mnemonic, rd, imm_iz_type);
        // lp.count
        3'b010: begin
          `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
          current_instr.str = $sformatf("%-16s 0x%0d, x%0d", mnemonic, rd, rs1);
        end
        // lp.counti
        3'b011: current_instr.str = $sformatf("%-16s x%0d, 0x%0h", mnemonic, rd, imm_iz_type);
        // lp.setup
        3'b100: begin
          `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
          current_instr.str = $sformatf("%-16s 0x%0d, x%0d, 0x%0h", mnemonic, rd, rs1, imm_iz_type);
        end
        // lp.setupi
        3'b101: begin
          current_instr.str = $sformatf("%-16s 0x%0d, 0x%0h, 0x%0h", mnemonic, rd, imm_iz_type, rs1);
        end
      endcase
    end
  endfunction // printHwloopInstr

  function void printLoadInstr();
    string mnemonic;
    logic [2:0] size;
    reg_t r;
    begin
      // detect reg-reg load and find size
      size = instr[14:12];
      if (instr[14:12] == 3'b111)
        size = instr[30:28];

      case (size)
        3'b000: mnemonic = "lb";
        3'b001: mnemonic = "lh";
        3'b010: mnemonic = "lw";
        3'b100: mnemonic = "lbu";
        3'b101: mnemonic = "lhu";
        3'b110: mnemonic = "p.elw";
        3'b011,
        3'b111: begin
          printMnemonic("INVALID");
          return;
        end
      endcase

      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);

      if (instr[14:12] != 3'b111) begin
        // regular load
        if (instr[6:0] != OPCODE_LOAD_POST) begin
          `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
          current_instr.str = $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, rd, $signed(imm_i_type), rs1);
        end else begin
          `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
          `ADDREG(current_instr.regs_write, r, rs1, 32'hDEADBEEF);
          current_instr.str = $sformatf("p.%-14s x%0d, %0d(x%0d!)", mnemonic, rd, $signed(imm_i_type), rs1);
        end
      end else begin
        // reg-reg load
        if (instr[6:0] != OPCODE_LOAD_POST) begin
          `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
          `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
          current_instr.str = $sformatf("%-16s x%0d, x%0d(x%0d)", mnemonic, rd, rs2, rs1);
        end else begin
          `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
          `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
          `ADDREG(current_instr.regs_write, r, rs1, 32'hDEADBEEF);
          current_instr.str = $sformatf("p.%-14s x%0d, x%0d(x%0d!)", mnemonic, rd, rs2, rs1);
        end
      end
    end
  endfunction //printLoadInstr

  function void printMulInstr();
    string mnemonic;
    string str_suf;
    string str_imm;
    string str_asm;
    reg_t r;
    begin

      // always read rs1 and rs2 and write rd
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);

      if (instr[12]) begin
        `ADDREG(current_instr.regs_read, r, rd, rs3_value);
      end

      case ({instr[31:30], instr[14]})
        3'b000: str_suf = "u";
        3'b001: str_suf = "uR";
        3'b010: str_suf = "hhu";
        3'b011: str_suf = "hhuR";
        3'b100: str_suf = "s";
        3'b101: str_suf = "sR";
        3'b110: str_suf = "hhs";
        3'b111: str_suf = "hhsR";
      endcase

      if (instr[12])
        mnemonic = "p.mac";
      else
        mnemonic = "p.mul";

      if (imm_s3_type[4:0] != 5'b00000)
        str_asm = $sformatf("%s%sN", mnemonic, str_suf);
      else
        str_asm = $sformatf("%s%s", mnemonic, str_suf);

      if (instr[29:25] != 5'b00000)
        current_instr.str = $sformatf("%-16s x%0d, x%0d, x%0d, %0d", str_asm, rd, rs1, rs2, $unsigned(imm_s3_type[4:0]));
      else
        current_instr.str = $sformatf("%-16s x%0d, x%0d, x%0d", str_asm, rd, rs1, rs2);
    end
  endfunction // printMulInstr

  function void printVecInstr();
    string mnemonic;
    string str_asm;
    string str_args;
    string str_hb;
    string str_sci;
    string str_imm;
    reg_t r;
    begin

      // always read rs1 and write rd
      `ADDREG(current_instr.regs_read, r, rs1, rs1_value);
      `ADDREG(current_instr.regs_write, r, rd, 32'hDEADBEEF);

      case (instr[14:13])
        2'b00: str_sci = "";
        2'b10: str_sci = ".sc";
        2'b11: str_sci = ".sci";
      endcase

      if (instr[12])
        str_hb = ".b";
      else
        str_hb = ".h";

      // set mnemonic
      case (instr[31:26])
        6'b000000: begin mnemonic = "pv.add";      str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b000010: begin mnemonic = "pv.sub";      str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b000100: begin mnemonic = "pv.avg";      str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b000110: begin mnemonic = "pv.avgu";     str_imm = $sformatf("0x%0d", imm_vu_type); end
        6'b001000: begin mnemonic = "pv.min";      str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b001010: begin mnemonic = "pv.minu";     str_imm = $sformatf("0x%0d", imm_vu_type); end
        6'b001100: begin mnemonic = "pv.max";      str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b001110: begin mnemonic = "pv.maxu";     str_imm = $sformatf("0x%0d", imm_vu_type); end
        6'b010000: begin mnemonic = "pv.srl";      str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b010010: begin mnemonic = "pv.sra";      str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b010100: begin mnemonic = "pv.sll";      str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b010110: begin mnemonic = "pv.or";       str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b011000: begin mnemonic = "pv.xor";      str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b011010: begin mnemonic = "pv.and";      str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b011100: begin mnemonic = "pv.abs";      str_imm = $sformatf("0x%0d", imm_vs_type); end

        6'b011110: begin mnemonic = "pv.extract";  str_imm = $sformatf("0x%0d", imm_vs_type); str_sci = ""; end
        6'b100100: begin mnemonic = "pv.extractu"; str_imm = $sformatf("0x%0d", imm_vu_type); str_sci = ""; end
        6'b101100: begin mnemonic = "pv.insert";   str_imm = $sformatf("0x%0d", imm_vs_type); end

        // shuffle/pack
        6'b110000: begin
          if (instr[14:12] == 3'b001) begin
              mnemonic = "pv.shuffle";
          end else begin
              mnemonic = "pv.shufflei0";
              str_imm = $sformatf("0x%0d", imm_shuffle_type);
          end
        end
        6'b111010: begin mnemonic = "pv.shufflei1"; str_imm = $sformatf("0x%0d", imm_shuffle_type);  end
        6'b111100: begin mnemonic = "pv.shufflei2"; str_imm = $sformatf("0x%0d", imm_shuffle_type);  end
        6'b111110: begin mnemonic = "pv.shufflei3"; str_imm = $sformatf("0x%0d", imm_shuffle_type);  end

        6'b110010: begin mnemonic = "pv.shuffle2"; end

        6'b110100: begin mnemonic = instr[25] ? "pv.pack.h" : "pv.pack"; end
        6'b110110: begin mnemonic = "pv.packhi";                         end
        6'b111000: begin mnemonic = "pv.packlo";                         end

        // comparisons
        6'b000001: begin mnemonic = "pv.cmpeq";    str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b000011: begin mnemonic = "pv.cmpne";    str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b000101: begin mnemonic = "pv.cmpgt";    str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b000111: begin mnemonic = "pv.cmpge";    str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b001001: begin mnemonic = "pv.cmplt";    str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b001011: begin mnemonic = "pv.cmple";    str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b001101: begin mnemonic = "pv.cmpgtu";   str_imm = $sformatf("0x%0d", imm_vu_type); end
        6'b001111: begin mnemonic = "pv.cmpgeu";   str_imm = $sformatf("0x%0d", imm_vu_type); end
        6'b010001: begin mnemonic = "pv.cmpltu";   str_imm = $sformatf("0x%0d", imm_vu_type); end
        6'b010011: begin mnemonic = "pv.cmpleu";   str_imm = $sformatf("0x%0d", imm_vu_type); end

        // dotproducts
        6'b100000: begin mnemonic = "pv.dotup";    str_imm = $sformatf("0x%0d", imm_vu_type); end
        6'b100010: begin mnemonic = "pv.dotusp";   str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b100110: begin mnemonic = "pv.dotsp";    str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b101000: begin mnemonic = "pv.sdotup";   str_imm = $sformatf("0x%0d", imm_vu_type); end
        6'b101010: begin mnemonic = "pv.sdotusp";  str_imm = $sformatf("0x%0d", imm_vs_type); end
        6'b101110: begin mnemonic = "pv.sdotsp";   str_imm = $sformatf("0x%0d", imm_vs_type); end

        6'b010101: begin
          unique case (instr[14:13])
              2'b00: mnemonic = instr[25] ? "pv.clpxmul.r"      : "pv.clpxmul.i";
              2'b01: mnemonic = instr[25] ? "pv.clpxmul.r.div2" : "pv.clpxmul.i.div2";
              2'b10: mnemonic = instr[25] ? "pv.clpxmul.r.div4" : "pv.clpxmul.i.div4";
              2'b11: mnemonic = instr[25] ? "pv.clpxmul.r.div8" : "pv.clpxmul.i.div8";
          endcase
          str_sci = "";
        end

        6'b011011: begin
          unique case (instr[14:13])
              2'b00: mnemonic = "pv.subrotmj";
              2'b01: mnemonic = "pv.subrotmj.div2";
              2'b10: mnemonic = "pv.subrotmj.div4";
              2'b11: mnemonic = "pv.subrotmj.div8";
          endcase
          str_sci = "";
        end

        6'b010111: begin mnemonic = "pv.cplxconj";  end

        6'b011101: begin
          unique case (instr[14:13])
              2'b01: mnemonic = "pv.add.div2";
              2'b10: mnemonic = "pv.add.div4";
              2'b11: mnemonic = "pv.add.div8";
          endcase
          str_sci = "";
        end

        6'b011001: begin
          unique case (instr[14:13])
              2'b01: mnemonic = "pv.sub.div2";
              2'b10: mnemonic = "pv.sub.div4";
              2'b11: mnemonic = "pv.sub.div8";
          endcase
          str_sci = "";
        end

        default: begin
          printMnemonic("INVALID");
          return;
        end
      endcase

      if (str_sci == "") begin
        `ADDREG(current_instr.regs_read, r, rs2, rs2_value);
        str_args = $sformatf("x%0d, x%0d, x%0d", rd, rs1, rs2);
      end else if (str_sci == ".sc") begin
        `ADDREG(current_instr.regs_read, r, rs2, rs2_value_vec);
        str_args = $sformatf("x%0d, x%0d, x%0d", rd, rs1, rs2);
      end else if (str_sci == ".sci") begin
        str_args = $sformatf("x%0d, x%0d, %s", rd, rs1, str_imm);
      end

      str_asm = $sformatf("%s%s%s", mnemonic, str_sci, str_hb);

      current_instr.str = $sformatf("%-16s %s", str_asm, str_args);
    end
  endfunction // printVecInstr


  function string regAddrToStr(input logic [5:0] addr);
      begin
        // TODO: use this function to also format the arguments to the
        // instructions
        if (SymbolicRegs) begin // format according to RISC-V ABI
          if (addr >= 42)
            return $sformatf(" f%0d", addr-32);
          else if (addr > 32)
            return $sformatf("  f%0d", addr-32);
          else begin
            if (addr == 0)
              return $sformatf("zero");
            else if (addr == 1)
              return $sformatf("  ra");
            else if (addr == 2)
              return $sformatf("  sp");
            else if (addr == 3)
              return $sformatf("  gp");
            else if (addr == 4)
              return $sformatf("  tp");
            else if (addr >= 5 && addr <= 7)
              return $sformatf("  t%0d", addr-5);
            else if (addr >= 8 && addr <= 9)
              return $sformatf("  s%0d", addr-8);
            else if (addr >= 10 && addr <= 17)
              return $sformatf("  a%0d", addr-10);
            else if (addr >= 18 && addr <= 25)
              return $sformatf("  s%0d", addr-16);
            else if (addr >= 26 && addr <= 27)
              return $sformatf(" s%0d", addr-16);
            else if (addr >= 28 && addr <= 31)
              return $sformatf("  t%0d", addr-25);
            else
              return $sformatf("UNKNOWN %0d", addr);
          end
        end else begin
          if (addr >= 42)
            return $sformatf("f%0d", addr-32);
          else if (addr > 32)
            return $sformatf(" f%0d", addr-32);
          else if (addr < 10)
            return $sformatf(" x%0d", addr);
          else
            return $sformatf("x%0d", addr);
        end
      end
  endfunction

  function void printInstrTrace();
    instr_trace_t trace;
    mem_acc_t mem_acc;
    if (to_print.size() > 0) begin
        trace = to_print.pop_front();

        $fwrite(f, "%21d %15d %h %h %-36s", trace.simtime,
                                          trace.cycles,
                                          trace.pc,
                                          trace.instr,
                                          trace.str);

        foreach(trace.regs_write[i]) begin
          if (trace.regs_write[i].addr != 0)
            $fwrite(f, " %s=%08x", regAddrToStr(trace.regs_write[i].addr), trace.regs_write[i].value);
        end

        foreach(trace.regs_read[i]) begin
          if (trace.regs_read[i].addr != 0)
            $fwrite(f, " %s:%08x", regAddrToStr(trace.regs_read[i].addr), trace.regs_read[i].value);
        end

        if (trace.mem_access.size() > 0) begin
          mem_acc = trace.mem_access.pop_front();

          $fwrite(f, "  PA:%08x", mem_acc.addr);
        end

        $fwrite(f, "\n");
        $fflush();

    end
  endfunction


  function void progressID();

    // special case for WFI because we don't wait for unstalling there
    if ( (id_valid || pipe_flush || mret || uret || ecall || ebreak || dret || fence) && is_decoding)
    begin
      current_instr = new ();

      current_instr.simtime    = $time;
      current_instr.cycles     = cycles;
      current_instr.pc         = pc;
      current_instr.instr      = instr;
      current_instr.run_ex     = 0;
      //$display("LOG: %08x time: %0d \n", current_instr.pc, cycles);

      // use casex instead of case inside due to ModelSim bug
      casex (instr)
        // Aliases
        32'h00_00_00_13:  printMnemonic("nop");
        // Regular opcodes
        INSTR_LUI:        printUInstr("lui");
        INSTR_AUIPC:      printUInstr("auipc");
        INSTR_JAL:        printUJInstr("jal");
        INSTR_JALR:       printIInstr("jalr");
        // BRANCH
        INSTR_BEQ:        printSBInstr("beq");
        INSTR_BNE:        printSBInstr("bne");
        INSTR_BLT:        printSBInstr("blt");
        INSTR_BGE:        printSBInstr("bge");
        INSTR_BLTU:       printSBInstr("bltu");
        INSTR_BGEU:       printSBInstr("bgeu");
        INSTR_BEQIMM:     printSBallInstr("p.beqimm");
        INSTR_BNEIMM:     printSBallInstr("p.bneimm");
        // OPIMM
        INSTR_ADDI:       printIInstr("addi");
        INSTR_SLTI:       printIInstr("slti");
        INSTR_SLTIU:      printIInstr("sltiu");
        INSTR_XORI:       printIInstr("xori");
        INSTR_ORI:        printIInstr("ori");
        INSTR_ANDI:       printIInstr("andi");
        INSTR_SLLI:       printIuInstr("slli");
        INSTR_SRLI:       printIuInstr("srli");
        INSTR_SRAI:       printIuInstr("srai");
        // OP
        INSTR_ADD:        printRInstr("add");
        INSTR_SUB:        printRInstr("sub");
        INSTR_SLL:        printRInstr("sll");
        INSTR_SLT:        printRInstr("slt");
        INSTR_SLTU:       printRInstr("sltu");
        INSTR_XOR:        printRInstr("xor");
        INSTR_SRL:        printRInstr("srl");
        INSTR_SRA:        printRInstr("sra");
        INSTR_OR:         printRInstr("or");
        INSTR_AND:        printRInstr("and");
        INSTR_EXTHS:      printRInstr("p.exths");
        INSTR_EXTHZ:      printRInstr("p.exthz");
        INSTR_EXTBS:      printRInstr("p.extbs");
        INSTR_EXTBZ:      printRInstr("p.extbz");
        INSTR_PAVG:       printRInstr("p.avg");
        INSTR_PAVGU:      printRInstr("p.avgu");

        INSTR_PADDN:      printAddNInstr("p.addN");
        INSTR_PADDUN:     printAddNInstr("p.adduN");
        INSTR_PADDRN:     printAddNInstr("p.addRN");
        INSTR_PADDURN:    printAddNInstr("p.adduRN");
        INSTR_PSUBN:      printAddNInstr("p.subN");
        INSTR_PSUBUN:     printAddNInstr("p.subuN");
        INSTR_PSUBRN:     printAddNInstr("p.subRN");
        INSTR_PSUBURN:    printAddNInstr("p.subuRN");

        INSTR_PADDNR:     printR3Instr("p.addNr");
        INSTR_PADDUNR:    printR3Instr("p.adduNr");
        INSTR_PADDRNR:    printR3Instr("p.addRNr");
        INSTR_PADDURNR:   printR3Instr("p.adduRNr");
        INSTR_PSUBNR:     printR3Instr("p.subNr");
        INSTR_PSUBUNR:    printR3Instr("p.subuNr");
        INSTR_PSUBRNR:    printR3Instr("p.subRNr");
        INSTR_PSUBURNR:   printR3Instr("p.subuRNr");

        INSTR_PSLET:      printRInstr("p.slet");
        INSTR_PSLETU:     printRInstr("p.sletu");
        INSTR_PMIN:       printRInstr("p.min");
        INSTR_PMINU:      printRInstr("p.minu");
        INSTR_PMAX:       printRInstr("p.max");
        INSTR_PMAXU:      printRInstr("p.maxu");
        INSTR_PABS:       printR1Instr("p.abs");
        INSTR_PCLIP:      printClipInstr("p.clip");
        INSTR_PCLIPU:     printClipInstr("p.clipu");
        INSTR_PBEXT:      printBit1Instr("p.extract");
        INSTR_PBEXTU:     printBit1Instr("p.extractu");
        INSTR_PBINS:      printBit2Instr("p.insert");
        INSTR_PBCLR:      printBit1Instr("p.bclr");
        INSTR_PBSET:      printBit1Instr("p.bset");
        INSTR_PBREV:      printBitRevInstr("p.bitrev");

        INSTR_PCLIPR:     printRInstr("p.clipr");
        INSTR_PCLIPUR:    printRInstr("p.clipur");
        INSTR_PBEXTR:     printRInstr("p.extractr");
        INSTR_PBEXTUR:    printRInstr("p.extractur");
        INSTR_PBINSR:     printR3Instr("p.insertr");
        INSTR_PBCLRR:     printRInstr("p.bclrr");
        INSTR_PBSETR:     printRInstr("p.bsetr");

        INSTR_FF1:        printR1Instr("p.ff1");
        INSTR_FL1:        printR1Instr("p.fl1");
        INSTR_CLB:        printR1Instr("p.clb");
        INSTR_CNT:        printR1Instr("p.cnt");
        INSTR_ROR:        printRInstr("p.ror");

        // FENCE
        INSTR_FENCE:      printMnemonic("fence");
        INSTR_FENCEI:     printMnemonic("fencei");
        // SYSTEM (CSR manipulation)
        INSTR_CSRRW:      printCSRInstr("csrrw");
        INSTR_CSRRS:      printCSRInstr("csrrs");
        INSTR_CSRRC:      printCSRInstr("csrrc");
        INSTR_CSRRWI:     printCSRInstr("csrrwi");
        INSTR_CSRRSI:     printCSRInstr("csrrsi");
        INSTR_CSRRCI:     printCSRInstr("csrrci");
        // SYSTEM (others)
        INSTR_ECALL:      printMnemonic("ecall");
        INSTR_EBREAK:     printMnemonic("ebreak");
        INSTR_URET:       printMnemonic("uret");
        INSTR_MRET:       printMnemonic("mret");
        INSTR_WFI:        printMnemonic("wfi");

        INSTR_DRET:       printMnemonic("dret");

        // RV32M
        INSTR_PMUL:       printRInstr("mul");
        INSTR_PMUH:       printRInstr("mulh");
        INSTR_PMULHSU:    printRInstr("mulhsu");
        INSTR_PMULHU:     printRInstr("mulhu");
        INSTR_DIV:        printRInstr("div");
        INSTR_DIVU:       printRInstr("divu");
        INSTR_REM:        printRInstr("rem");
        INSTR_REMU:       printRInstr("remu");
        // PULP MULTIPLIER
        INSTR_PMAC:       printR3Instr("p.mac");
        INSTR_PMSU:       printR3Instr("p.msu");
        INSTR_PMULS     : printMulInstr();
        INSTR_PMULHLSN  : printMulInstr();
        INSTR_PMULRS    : printMulInstr();
        INSTR_PMULRHLSN : printMulInstr();
        INSTR_PMULU     : printMulInstr();
        INSTR_PMULUHLU  : printMulInstr();
        INSTR_PMULRU    : printMulInstr();
        INSTR_PMULRUHLU : printMulInstr();
        INSTR_PMACS     : printMulInstr();
        INSTR_PMACHLSN  : printMulInstr();
        INSTR_PMACRS    : printMulInstr();
        INSTR_PMACRHLSN : printMulInstr();
        INSTR_PMACU     : printMulInstr();
        INSTR_PMACUHLU  : printMulInstr();
        INSTR_PMACRU    : printMulInstr();
        INSTR_PMACRUHLU : printMulInstr();

        // FP-OP
        INSTR_FMADD:      printF3Instr("fmadd.s");
        INSTR_FMSUB:      printF3Instr("fmsub.s");
        INSTR_FNMADD:     printF3Instr("fnmadd.s");
        INSTR_FNMSUB:     printF3Instr("fnmsub.s");
        INSTR_FADD:       printF2Instr("fadd.s");
        INSTR_FSUB:       printF2Instr("fsub.s");
        INSTR_FMUL:       printF2Instr("fmul.s");
        INSTR_FDIV:       printF2Instr("fdiv.s");
        INSTR_FSQRT:      printFInstr("fsqrt.s");
        INSTR_FSGNJS:     printF2Instr("fsgnj.s");
        INSTR_FSGNJNS:    printF2Instr("fsgnjn.s");
        INSTR_FSGNJXS:    printF2Instr("fsgnjx.s");
        INSTR_FMIN:       printF2Instr("fmin.s");
        INSTR_FMAX:       printF2Instr("fmax.s");
        INSTR_FCVTWS:     printFIInstr("fcvt.w.s");
        INSTR_FCVTWUS:    printFIInstr("fcvt.wu.s");
        INSTR_FMVXS:      printFIInstr("fmv.x.s");
        INSTR_FEQS:       printF2IInstr("feq.s");
        INSTR_FLTS:       printF2IInstr("flt.s");
        INSTR_FLES:       printF2IInstr("fle.s");
        INSTR_FCLASS:     printFIInstr("fclass.s");
        INSTR_FCVTSW:     printIFInstr("fcvt.s.w");
        INSTR_FCVTSWU:    printIFInstr("fcvt.s.wu");
        INSTR_FMVSX:      printIFInstr("fmv.s.x");

        // RV32A
        INSTR_LR:         printAtomicInstr("lr.w");
        INSTR_SC:         printAtomicInstr("sc.w");
        INSTR_AMOSWAP:    printAtomicInstr("amoswap.w");
        INSTR_AMOADD:     printAtomicInstr("amoadd.w");
        INSTR_AMOXOR:     printAtomicInstr("amoxor.w");
        INSTR_AMOAND:     printAtomicInstr("amoand.w");
        INSTR_AMOOR:      printAtomicInstr("amoor.w");
        INSTR_AMOMIN:     printAtomicInstr("amomin.w");
        INSTR_AMOMAX:     printAtomicInstr("amomax.w");
        INSTR_AMOMINU:    printAtomicInstr("amominu.w");
        INSTR_AMOMAXU:    printAtomicInstr("amomaxu.w");

        // opcodes with custom decoding
        {25'b?, OPCODE_LOAD}:           printLoadInstr();
        {25'b?, OPCODE_LOAD_FP}:        printLoadInstr();
        {25'b?, OPCODE_LOAD_POST}:      printLoadInstr();
        {25'b?, OPCODE_STORE}:          printStoreInstr();
        {25'b?, OPCODE_STORE_FP}:       printStoreInstr();
        {25'b?, OPCODE_STORE_POST}:     printStoreInstr();
        {25'b?, OPCODE_STORE_BUF}:      printStoreBuffInstr();
        {25'b?, OPCODE_STORE_POST_BUF}: printStoreBuffInstr();
        {25'b?, OPCODE_HWLOOP}:         printHwloopInstr();
        {25'b?, OPCODE_VECOP}:          printVecInstr();
        default:                        printMnemonic("INVALID");
      endcase // unique case (instr)
      
      instr_ex.push_back(current_instr);
    end
  endfunction

  function void progressEX();
    instr_trace_t trace;
    instr_trace_t trace_pop;
    mem_acc_t     mem_acc;

    if (instr_ex.size() > 0) begin
      trace = instr_ex.pop_front(); 

      //$display("EX: %08x time: %0d \n", trace.pc, cycles);

      foreach(trace.regs_write[i]) begin
        if ((trace.regs_write[i].addr == ex_reg_addr) && ex_reg_we) begin
            trace.regs_write[i].value = ex_reg_wdata;
        end
      end

      if (ex_data_req && ex_data_gnt) begin
        mem_acc.addr = ex_data_addr;
        mem_acc.we   = ex_data_we;

        if (mem_acc.we) begin
          mem_acc.wdata = ex_data_wdata;
        end else begin
          mem_acc.wdata = 32'hDEADBEEF;
        end

        trace.mem_access.push_back(mem_acc);
      end

      if (ex_valid || wb_bypass) begin
        if(ex_data_req && data_misaligned) begin
          instr_ex_misaligned.push_back(trace);
        end else begin
          instr_wb.push_back(trace);
        end

        // NOTE: verilator seems to not like pop_front as standalone (i.e., without assignment) statement.
        //trace_pop = instr_ex.pop_front();    
      end else begin
        // NOTE: we don't have a front() method (?) and instr_ex[0] has not queue semantic. Verilator 
        // maps queue operations to std::deque, so pushing/popping have O(1) complexity
        instr_ex.push_front(trace);
      end
    end
  endfunction
  
  function void progressEXMisaligned();
    instr_trace_t trace;
    instr_trace_t trace_pop;

    if (instr_ex_misaligned.size() > 0) begin
      trace = instr_ex_misaligned.pop_front();
      //$display("EXM: %08x time: %0d \n", trace.pc, cycles);
      if (ex_valid || wb_bypass) begin
        instr_wb.push_back(trace);
        // NOTE: verilator seems to not like pop_front as standalone (i.e., without assignment) statement.
        //trace_pop = instr_ex_misaligned.pop_front();
      end else begin
        instr_ex_misaligned.push_front(trace);
      end
    end
  endfunction

  function void progressWB();
    instr_trace_t trace;
    instr_trace_t trace_pop;
    if (instr_wb.size() > 0) begin
      trace = instr_wb.pop_front();
      foreach(trace.regs_write[i]) begin
        //$display("WB: %0d; wb_reg_addr: %08x; wb_reg_wdata: %08x\n", trace.instr, wb_reg_addr, wb_reg_wdata);
        //$display("WB: %08x time: %0d \n", trace.pc, cycles);

        if ((trace.regs_write[i].addr == wb_reg_addr) && wb_reg_we) begin
          trace.regs_write[i].value = wb_reg_wdata;
        end
      end

      if (wb_valid) begin
        to_print.push_back(trace);
        // NOTE: verilator seems to not like pop_front as standalone (i.e., without assignment) statement.
        //trace_pop = instr_wb.pop_front();      
      end else begin
        instr_wb.push_front(trace);
      end 
    end
  endfunction

  // cycle counter
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0)
      cycles <= 0;
    else
      cycles <= cycles + 1;
  end

  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
        state <= Init;
        f = 0;
    end else begin
        state <= Running;
        if (f == 0) begin
            $sformat(fn, "trace_core_%h_%h.log", hart_id_i[10:5], hart_id_i[3:0]);
            // $display("[TRACER] Output filename is: %s", fn);
            f = $fopen(fn, "w");
            $fwrite(f, "                Time           Cycles PC       Instr    Mnemonic\n");
        end
    end
  end

  final
  begin
    $fclose(f);
  end

  // log execution
  always @(negedge clk)
  begin

    if (state == Running) begin
      //we run the stages in reverse order because we don't want the same instr being 
      //processed by the multiple stages in the same cycle.
      progressWB();
      progressEXMisaligned();
      progressEX();
      progressID();

      printInstrTrace();
    end
  end // always @ (posedge clk)

endmodule
