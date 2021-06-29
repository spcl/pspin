// Copyright 2020 ETH Zurich and University of Bologna.
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

import pspin_tb_cfg_pkg::*;
import pspin_cfg_pkg::*;

module packet_generator #(
  parameter string DataFilePath = "",
  parameter string TaskFilePath = "",
  parameter time TA = 0ps,
  parameter time TT = 0ps,
  parameter int TOT_NUM_CORES = 32,
  parameter int NUM_CLUSTERS = 4,
  parameter longint unsigned PKT_MEM_START = 0,
  parameter int unsigned Verbosity = 0,
  parameter int N_MPQ = 0,
  parameter int PKT_MEM_SIZE = 4*1024*1024 // [B]
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,

  //output interface to scheduler
  input  logic                        her_ready_i,
  output logic                        her_valid_o,
  output pspin_cfg_pkg::her_descr_t   her_descr_o,

  output logic                        eos_o,

  //input interface from scheduler
  input  logic                        feedback_valid_i,
  output logic                        feedback_ready_o,
  input  pspin_cfg_pkg::feedback_descr_t  feedback_i,

  input  logic                        pspin_active_i
);

  
  typedef logic [7:0] byte_t;

  logic can_start;
  logic [31:0] num_feedbacks_q;
  logic [31:0] num_feedbacks_d;

  assign num_feedbacks_d = (feedback_valid_i && feedback_ready_o) ? num_feedbacks_q + 1 : num_feedbacks_q;

  assign can_start = pspin_active_i;

  pspin_cfg_pkg::her_descr_t her_descriptors_waiting[$];
  pspin_cfg_pkg::her_descr_t her_descriptors_ready[$];

  task sleep(input int unsigned cycles);
    for (int unsigned i = 0; i < cycles; i++) begin
      @(posedge clk_i);
    end
  endtask


  always_ff @(posedge clk_i) begin
    if (~rst_ni) begin
      num_feedbacks_q <= 0;
    end else begin
      num_feedbacks_q <= num_feedbacks_d;
    end
  end

  initial begin
    her_valid_o = 1'b0;
    wait (rst_ni);
    forever begin
      static pspin_cfg_pkg::her_descr_t her_descr;
      her_valid_o = 1'b0;
      //@(posedge clk_i);
      if (her_descriptors_ready.size == 0) begin
        @(posedge clk_i);
        continue;
      end

      her_descr = her_descriptors_ready.pop_front();
      her_descr_o = her_descr;
      her_valid_o = 1'b1;
      //$display("%0d INFO PKT_SENT", $stime);
      do begin
        @(posedge clk_i);
      end
      while (!her_ready_i);
    end
  end

  int unsigned cnt;
  initial begin
    cnt = 0;
    wait (rst_ni);
    forever begin
      @(posedge clk_i);
      if (cnt > 0) begin
        cnt -= 1;
      end
    end
  end


  //for now we just consume the feedbacks here
  assign feedback_ready_o = 1'b1;

  // Generate packets from files.
  initial begin
    static addr_t write_ptr, read_ptr;
    static int data_fd, task_fd;
    static pspin_cfg_pkg::her_descr_t her_descr;
    //static int pkt_idx;

    //pkt_idx = 0;
    her_valid_o = 0;
    eos_o = 1'b0;

    // Open files.
    data_fd = $fopen(DataFilePath, "rb");
    if (data_fd == 0) begin
      $error("Failed to open data file!");
      forever begin
        @(posedge clk_i);
      end
    end
    task_fd = $fopen(TaskFilePath, "r");
    if (task_fd == 0) begin
      $error("Failed to open task file!");
      forever begin
        @(posedge clk_i);
      end
    end
    // Reset write pointer.
    write_ptr = PKT_MEM_START;
    wait (rst_ni);

    wait (can_start);

    // Iterate line by line through task file.
    while (!$feof(task_fd)) begin
      automatic int unsigned msgid;
      automatic int unsigned hh_addr, hh_size, ph_addr, ph_size, th_addr, th_size;
      automatic int unsigned hmem_addr, hmem_size;
      automatic int unsigned pkt_size, pkt_xfer_size;
      automatic int unsigned eom, wait_cycles;
      automatic byte_t buffer[];
      automatic int code;
      // Read task file.
      code = $fscanf(task_fd, "%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d\n", msgid, hh_addr, hh_size, ph_addr, ph_size, th_addr, th_size, hmem_addr, hmem_size, pkt_size, pkt_xfer_size, eom, wait_cycles);
      if (code != 13) begin
        $error("Failed to properly read task line!");
        continue;
      end

      if (Verbosity >= 2) begin
        $display("New task: %0d bytes and %0d cycles.", pkt_size, wait_cycles);
      end


      // Set counter.
      cnt = wait_cycles;
      // Read required number of bytes from data file.
      buffer = new[pkt_size];

      code = $fread(buffer, data_fd, 0, pkt_size);
      if (code != pkt_size) begin
        $error("Could only read %0d bytes from file!", code);
        continue;
      end

      if (Verbosity >= 2) begin
        $display("Writing %0d bytes, starting at 0x%08x.", pkt_size, write_ptr);
      end
      // send handler execution request to the scheduler
      her_descr.mpq_meta.hh_addr[C_ADDR_WIDTH-1:0] = 32'h1e000040; //hh_addr;
      her_descr.mpq_meta.hh_size[C_SIZE_WIDTH-1:0] = hh_size;
      
      her_descr.mpq_meta.ph_addr[C_ADDR_WIDTH-1:0] = 32'h1e000040; //ph_addr;
      her_descr.mpq_meta.ph_size[C_SIZE_WIDTH-1:0] = ph_size;
      
      her_descr.mpq_meta.th_addr[C_ADDR_WIDTH-1:0] = 32'h1e000040; //th_addr;
      her_descr.mpq_meta.th_size[C_SIZE_WIDTH-1:0] = th_size;

      her_descr.mpq_meta.handler_mem_addr[C_ADDR_WIDTH-1:0] = hmem_addr;
      her_descr.mpq_meta.handler_mem_size[C_SIZE_WIDTH-1:0] = hmem_size;
      
      her_descr.mpq_meta.host_mem_addr[C_HOST_ADDR_WIDTH-1:0] = 64'h0000_0000_0000_0000;
      her_descr.mpq_meta.host_mem_size[C_SIZE_WIDTH-1:0] = 32'h4000_0000;

      her_descr.mpq_meta.pin_to_cluster = 1'b1;

      for (int i=0; i<pspin_cfg_pkg::NUM_CLUSTERS; i++) begin
        her_descr.mpq_meta.scratchpad_addr[i] = 0;
        her_descr.mpq_meta.scratchpad_size[i] = pspin_cfg_pkg::L1_SCRATCHPAD_SIZE;
      end

      her_descr.msgid[C_MSGID_WIDTH-1:0] = msgid;
      her_descr.her_addr[C_ADDR_WIDTH-1:0]  = write_ptr;
      her_descr.her_size[C_SIZE_WIDTH-1:0]  = pkt_size;
      her_descr.xfer_size[C_SIZE_WIDTH-1:0] = pkt_xfer_size;
      her_descr.eom = (eom==1);

      her_descriptors_waiting.push_back(her_descr);

      write_ptr += pkt_size;

      her_descr = her_descriptors_waiting.pop_front();
      her_descriptors_ready.push_back(her_descr);

      if (cnt > 0) begin
        if (Verbosity >= 2) begin
          $display("Sleeping for %0d cycles.", cnt);
        end  
        sleep(cnt);
      end
    end

    wait (her_descriptors_ready.size == 0 && her_descriptors_waiting.size == 0)
    eos_o = 1'b1;
    if (Verbosity >= 1) begin
      $display("All packets written.");
    end
  end

endmodule
