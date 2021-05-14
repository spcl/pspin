`include "axi/assign.svh"
`include "axi/typedef.svh"

import pspin_cfg_pkg::*;

module pspin_tb #();

    timeunit 1ps;
    timeprecision 1ps;

    localparam time                      CLK_PERIOD = 1ns;

    typedef logic [AXI_SOC_AW-1:0]      addr_t;
    typedef logic [AXI_HOST_AW-1:0]     host_addr_t;
    typedef logic [AXI_WIDE_DW-1:0]     wide_data_t;
    typedef logic [AXI_WIDE_DW/8-1:0]   wide_strb_t;
    typedef logic [AXI_NARROW_DW-1:0]   narrow_data_t;
    typedef logic [AXI_NARROW_DW/8-1:0] narrow_strb_t;
    typedef logic [AXI_IW-1:0]          id_t;
    typedef logic [AXI_UW-1:0]          user_t;

    `AXI_TYPEDEF_ALL(nic_wide, addr_t, id_t, wide_data_t, wide_strb_t, user_t)
    `AXI_TYPEDEF_ALL(host_out, host_addr_t, id_t, wide_data_t, wide_strb_t, user_t)
    `AXI_TYPEDEF_ALL(host_in, addr_t, id_t, wide_data_t, wide_strb_t, user_t)

    host_in_req_t                       host_in_req;
    host_in_resp_t                      host_in_resp;
    host_out_req_t                      host_out_req;
    host_out_resp_t                     host_out_resp;
    nic_wide_req_t                      ni_req, no_req;
    nic_wide_resp_t                     ni_resp, no_resp;

    // pktgen -> pspin
    logic                               her_valid;
    logic                               her_ready;
    pspin_cfg_pkg::her_descr_t          her;
    logic                               eos;

    // pspin -> pktgen
    logic                               feedback_valid;
    logic                               feedback_ready;
    pspin_cfg_pkg::feedback_descr_t     feedback;

    logic                               pspin_active;

    // pspin -> nic outbound
    logic                               nic_cmd_ready;
    logic                               nic_cmd_valid;
    pspin_cfg_pkg::pspin_cmd_t          nic_cmd;
    logic                               nic_cmd_resp_valid;
    pspin_cfg_pkg::pspin_cmd_resp_t     nic_cmd_resp;

    logic                               clk, rst_n;

    clk_rst_gen #(
        .CLK_PERIOD     (CLK_PERIOD),
        .RST_CLK_CYCLES (10)
    ) i_clk_gen (
        .clk_o  (clk),
        .rst_no (rst_n)
    );

    pspin #(
        .host_in_req_t (host_in_req_t),
        .host_in_resp_t (host_in_resp_t),
        .host_out_req_t (host_out_req_t),
        .host_out_resp_t (host_out_resp_t),
        .ni_in_req_t (nic_wide_req_t),
        .ni_in_resp_t (nic_wide_resp_t),
        .no_in_req_t (nic_wide_req_t),
        .no_in_resp_t (nic_wide_resp_t)
    ) i_pspin (
        .clk_i                  (clk),
        .rst_ni                 (rst_n),
        
        .host_wide_req_i        (host_in_req),
        .host_wide_resp_o       (host_in_resp),
        .host_wide_req_o        (host_out_req),
        .host_wide_resp_i       (host_out_resp),

        .her_ready_o            (her_ready),
        .her_valid_i            (her_valid),
        .her_i                  (her),
        .ni_wide_req_i          (ni_req),
        .ni_wide_resp_o         (ni_resp),

        .nic_feedback_ready_i   (feedback_ready),
        .nic_feedback_valid_o   (feedback_valid),
        .nic_feedback_o         (feedback),

        .nic_cmd_ready_i        (nic_cmd_ready),
        .nic_cmd_valid_o        (nic_cmd_valid),
        .nic_cmd_o              (nic_cmd),

        .nic_cmd_resp_valid_i   (nic_cmd_resp_valid),
        .nic_cmd_resp_i         (nic_cmd_resp),
 
        .no_wide_req_i          (no_req),
        .no_wide_resp_o         (no_resp),

        .eos_i                  (eos),
        .pspin_active_o         (pspin_active)
    );

    initial begin
        $display("init!");
        wait (rst_n);
        $display("starting!");
        //wait(dut.i_mpq_engine.mpq_busy == '0 && dut.i_mpq_engine.eos_i && dut.i_mpq_engine.fifo_empty);
        #10us
        //wait (0);
        $display("ending!");
        //print_clusters_stats();
        $finish(1);
    end

    initial begin
        wait (rst_n);
        $readmemh("./prog_mem_stim.slm", i_pspin.i_prog_mem.i_sram.i_tc_sram.sram);
    end




endmodule