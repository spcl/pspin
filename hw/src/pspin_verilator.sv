// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

import pspin_cfg_pkg::*;

package automatic pspin_io;

    typedef logic [pspin_cfg_pkg::HOST_AXI_AW-1:0]    wide_addr_t;
    typedef logic [pspin_cfg_pkg::AXI_AW-1:0]         addr_t;
    typedef logic [pspin_cfg_pkg::AXI_WIDE_DW-1:0]    data_t;
    typedef logic [pspin_cfg_pkg::AXI_WIDE_DW/8-1:0]  strb_t;
    typedef logic [pspin_cfg_pkg::AXI_IW-1:0]         id_t;
    typedef logic [pspin_cfg_pkg::AXI_UW-1:0]         user_t;

endpackage

module pspin_verilator #(
) (
    /** Clocks and Resets **/
    input  logic                            clk_i,
    input  logic                            rst_ni,

    // asserted when HPUs are ready
    output logic                            pspin_active_o,

    // termination signal 
    input  logic                            eos_i,

    // MPQ full signal
    output logic [NUM_MPQ-1:0]              mpq_full_o,         


    /** NIC inbound engine AXI slave port **/
    // WRITE ADDRESS CHANNEL
    input  pspin_io::addr_t                 ni_slave_aw_addr_i,
    input  axi_pkg::prot_t                  ni_slave_aw_prot_i,
    input  axi_pkg::region_t                ni_slave_aw_region_i,
    input  axi_pkg::len_t                   ni_slave_aw_len_i,
    input  axi_pkg::size_t                  ni_slave_aw_size_i,
    input  axi_pkg::burst_t                 ni_slave_aw_burst_i,
    input  logic                            ni_slave_aw_lock_i,
    input  axi_pkg::atop_t                  ni_slave_aw_atop_i,
    input  axi_pkg::cache_t                 ni_slave_aw_cache_i,
    input  axi_pkg::qos_t                   ni_slave_aw_qos_i,
    input  pspin_io::id_t                   ni_slave_aw_id_i,
    input  pspin_io::user_t                 ni_slave_aw_user_i,
    input  logic                            ni_slave_aw_valid_i,
    output logic                            ni_slave_aw_ready_o,

    // READ ADDRESS CHANNEL
    input  pspin_io::addr_t                 ni_slave_ar_addr_i,
    input  axi_pkg::prot_t                  ni_slave_ar_prot_i,
    input  axi_pkg::region_t                ni_slave_ar_region_i,
    input  axi_pkg::len_t                   ni_slave_ar_len_i,
    input  axi_pkg::size_t                  ni_slave_ar_size_i,
    input  axi_pkg::burst_t                 ni_slave_ar_burst_i,
    input  logic                            ni_slave_ar_lock_i,
    input  axi_pkg::cache_t                 ni_slave_ar_cache_i,
    input  axi_pkg::qos_t                   ni_slave_ar_qos_i,
    input  pspin_io::id_t                   ni_slave_ar_id_i,
    input  pspin_io::user_t                 ni_slave_ar_user_i,
    input  logic                            ni_slave_ar_valid_i,
    output logic                            ni_slave_ar_ready_o,

    // WRITE DATA CHANNEL
    input  pspin_io::data_t                 ni_slave_w_data_i,
    input  pspin_io::strb_t                 ni_slave_w_strb_i,
    input  pspin_io::user_t                 ni_slave_w_user_i,
    input  logic                            ni_slave_w_last_i,
    input  logic                            ni_slave_w_valid_i,
    output logic                            ni_slave_w_ready_o,

    // READ DATA CHANNEL
    output pspin_io::data_t                 ni_slave_r_data_o,
    output axi_pkg::resp_t                  ni_slave_r_resp_o,
    output logic                            ni_slave_r_last_o,
    output pspin_io::id_t                   ni_slave_r_id_o,
    output pspin_io::user_t                 ni_slave_r_user_o,
    output logic                            ni_slave_r_valid_o,
    input  logic                            ni_slave_r_ready_i,

    // WRITE RESPONSE CHANNEL
    output axi_pkg::resp_t                  ni_slave_b_resp_o,
    output pspin_io::id_t                   ni_slave_b_id_o,
    output pspin_io::user_t                 ni_slave_b_user_o,
    output logic                            ni_slave_b_valid_o,
    input  logic                            ni_slave_b_ready_i,


    /** NIC outbound engine AXI slave port **/
    // WRITE ADDRESS CHANNEL
    input  pspin_io::addr_t                 no_slave_aw_addr_i,
    input  axi_pkg::prot_t                  no_slave_aw_prot_i,
    input  axi_pkg::region_t                no_slave_aw_region_i,
    input  axi_pkg::len_t                   no_slave_aw_len_i,
    input  axi_pkg::size_t                  no_slave_aw_size_i,
    input  axi_pkg::burst_t                 no_slave_aw_burst_i,
    input  logic                            no_slave_aw_lock_i,
    input  axi_pkg::atop_t                  no_slave_aw_atop_i,
    input  axi_pkg::cache_t                 no_slave_aw_cache_i,
    input  axi_pkg::qos_t                   no_slave_aw_qos_i,
    input  pspin_io::id_t                   no_slave_aw_id_i,
    input  pspin_io::user_t                 no_slave_aw_user_i,
    input  logic                            no_slave_aw_valid_i,
    output logic                            no_slave_aw_ready_o,

    // READ ADDRESS CHANNEL
    input  pspin_io::addr_t                 no_slave_ar_addr_i,
    input  axi_pkg::prot_t                  no_slave_ar_prot_i,
    input  axi_pkg::region_t                no_slave_ar_region_i,
    input  axi_pkg::len_t                   no_slave_ar_len_i,
    input  axi_pkg::size_t                  no_slave_ar_size_i,
    input  axi_pkg::burst_t                 no_slave_ar_burst_i,
    input  logic                            no_slave_ar_lock_i,
    input  axi_pkg::cache_t                 no_slave_ar_cache_i,
    input  axi_pkg::qos_t                   no_slave_ar_qos_i,
    input  pspin_io::id_t                   no_slave_ar_id_i,
    input  pspin_io::user_t                 no_slave_ar_user_i,
    input  logic                            no_slave_ar_valid_i,
    output logic                            no_slave_ar_ready_o,

    // WRITE DATA CHANNEL
    input  pspin_io::data_t                 no_slave_w_data_i,
    input  pspin_io::strb_t                 no_slave_w_strb_i,
    input  pspin_io::user_t                 no_slave_w_user_i,
    input  logic                            no_slave_w_last_i,
    input  logic                            no_slave_w_valid_i,
    output logic                            no_slave_w_ready_o,

    // READ DATA CHANNEL
    output pspin_io::data_t                 no_slave_r_data_o,
    output axi_pkg::resp_t                  no_slave_r_resp_o,
    output logic                            no_slave_r_last_o,
    output pspin_io::id_t                   no_slave_r_id_o,
    output pspin_io::user_t                 no_slave_r_user_o,
    output logic                            no_slave_r_valid_o,
    input  logic                            no_slave_r_ready_i,

    // WRITE RESPONSE CHANNEL
    output axi_pkg::resp_t                  no_slave_b_resp_o,
    output pspin_io::id_t                   no_slave_b_id_o,
    output pspin_io::user_t                 no_slave_b_user_o,
    output logic                            no_slave_b_valid_o,
    input  logic                            no_slave_b_ready_i,


    /** host AXI slave port **/
    // WRITE ADDRESS CHANNEL
    input  pspin_io::addr_t                 host_slave_aw_addr_i,
    input  axi_pkg::prot_t                  host_slave_aw_prot_i,
    input  axi_pkg::region_t                host_slave_aw_region_i,
    input  axi_pkg::len_t                   host_slave_aw_len_i,
    input  axi_pkg::size_t                  host_slave_aw_size_i,
    input  axi_pkg::burst_t                 host_slave_aw_burst_i,
    input  logic                            host_slave_aw_lock_i,
    input  axi_pkg::atop_t                  host_slave_aw_atop_i,
    input  axi_pkg::cache_t                 host_slave_aw_cache_i,
    input  axi_pkg::qos_t                   host_slave_aw_qos_i,
    input  pspin_io::id_t                   host_slave_aw_id_i,
    input  pspin_io::user_t                 host_slave_aw_user_i,
    input  logic                            host_slave_aw_valid_i,
    output logic                            host_slave_aw_ready_o,

    // READ ADDRESS CHANNEL
    input  pspin_io::addr_t                 host_slave_ar_addr_i,
    input  axi_pkg::prot_t                  host_slave_ar_prot_i,
    input  axi_pkg::region_t                host_slave_ar_region_i,
    input  axi_pkg::len_t                   host_slave_ar_len_i,
    input  axi_pkg::size_t                  host_slave_ar_size_i,
    input  axi_pkg::burst_t                 host_slave_ar_burst_i,
    input  logic                            host_slave_ar_lock_i,
    input  axi_pkg::cache_t                 host_slave_ar_cache_i,
    input  axi_pkg::qos_t                   host_slave_ar_qos_i,
    input  pspin_io::id_t                   host_slave_ar_id_i,
    input  pspin_io::user_t                 host_slave_ar_user_i,
    input  logic                            host_slave_ar_valid_i,
    output logic                            host_slave_ar_ready_o,

    // WRITE DATA CHANNEL
    input  pspin_io::data_t                 host_slave_w_data_i,
    input  pspin_io::strb_t                 host_slave_w_strb_i,
    input  pspin_io::user_t                 host_slave_w_user_i,
    input  logic                            host_slave_w_last_i,
    input  logic                            host_slave_w_valid_i,
    output logic                            host_slave_w_ready_o,

    // READ DATA CHANNEL
    output pspin_io::data_t                 host_slave_r_data_o,
    output axi_pkg::resp_t                  host_slave_r_resp_o,
    output logic                            host_slave_r_last_o,
    output pspin_io::id_t                   host_slave_r_id_o,
    output pspin_io::user_t                 host_slave_r_user_o,
    output logic                            host_slave_r_valid_o,
    input  logic                            host_slave_r_ready_i,

    // WRITE RESPONSE CHANNEL
    output axi_pkg::resp_t                  host_slave_b_resp_o,
    output pspin_io::id_t                   host_slave_b_id_o,
    output pspin_io::user_t                 host_slave_b_user_o,
    output logic                            host_slave_b_valid_o,
    input  logic                            host_slave_b_ready_i,


    /** host AXI master port **/
    // WRITE ADDRESS CHANNEL
    output pspin_io::wide_addr_t            host_master_aw_addr_o,
    output axi_pkg::prot_t                  host_master_aw_prot_o,
    output axi_pkg::region_t                host_master_aw_region_o,
    output axi_pkg::len_t                   host_master_aw_len_o,
    output axi_pkg::size_t                  host_master_aw_size_o,
    output axi_pkg::burst_t                 host_master_aw_burst_o,
    output logic                            host_master_aw_lock_o,
    output axi_pkg::atop_t                  host_master_aw_atop_o,
    output axi_pkg::cache_t                 host_master_aw_cache_o,
    output axi_pkg::qos_t                   host_master_aw_qos_o,
    output pspin_io::id_t                   host_master_aw_id_o,
    output pspin_io::user_t                 host_master_aw_user_o,
    output logic                            host_master_aw_valid_o,
    input  logic                            host_master_aw_ready_i,

    // READ ADDRESS CHANNEL
    output pspin_io::wide_addr_t            host_master_ar_addr_o,
    output axi_pkg::prot_t                  host_master_ar_prot_o,
    output axi_pkg::region_t                host_master_ar_region_o,
    output axi_pkg::len_t                   host_master_ar_len_o,
    output axi_pkg::size_t                  host_master_ar_size_o,
    output axi_pkg::burst_t                 host_master_ar_burst_o,
    output logic                            host_master_ar_lock_o,
    output axi_pkg::cache_t                 host_master_ar_cache_o,
    output axi_pkg::qos_t                   host_master_ar_qos_o,
    output pspin_io::id_t                   host_master_ar_id_o,
    output pspin_io::user_t                 host_master_ar_user_o,
    output logic                            host_master_ar_valid_o,
    input  logic                            host_master_ar_ready_i,

    // WRITE DATA CHANNEL
    output pspin_io::data_t                 host_master_w_data_o,
    output pspin_io::strb_t                 host_master_w_strb_o,
    output pspin_io::user_t                 host_master_w_user_o,
    output logic                            host_master_w_last_o,
    output logic                            host_master_w_valid_o,
    input  logic                            host_master_w_ready_i,

    // READ DATA CHANNEL
    input  pspin_io::data_t                 host_master_r_data_i,
    input  axi_pkg::resp_t                  host_master_r_resp_i,
    input  logic                            host_master_r_last_i,
    input  pspin_io::id_t                   host_master_r_id_i,
    input  pspin_io::user_t                 host_master_r_user_i,
    input  logic                            host_master_r_valid_i,
    output logic                            host_master_r_ready_o,

    // WRITE RESPONSE CHANNEL
    input  axi_pkg::resp_t                  host_master_b_resp_i,
    input  pspin_io::id_t                   host_master_b_id_i,
    input  pspin_io::user_t                 host_master_b_user_i,
    input  logic                            host_master_b_valid_i,
    output logic                            host_master_b_ready_o,


    /** NIC inbound engine/packet generator control **/
    //from pktgen
    output logic                            task_ready_o,
    input  logic                            task_valid_i,
    input  logic [C_MSGID_WIDTH-1:0]        task_msgid_i,
    input  mem_addr_t                       task_pkt_addr_i,
    input  mem_size_t                       task_pkt_size_i,
    input  mem_addr_t                       task_l2_mem_addr_i,
    input  mem_size_t                       task_l2_mem_size_i,
    input  host_addr_t                      task_host_mem_addr_i,
    input  mem_size_t                       task_host_mem_size_i,
    input  mem_addr_t                       task_handler_addr_i,
    input  mem_size_t                       task_handler_size_i,
    input  mem_addr_t                       task_scratchpad_0_addr_i,
    input  mem_size_t                       task_scratchpad_0_size_i,
    input  mem_addr_t                       task_scratchpad_1_addr_i,
    input  mem_size_t                       task_scratchpad_1_size_i,
    input  mem_addr_t                       task_scratchpad_2_addr_i,
    input  mem_size_t                       task_scratchpad_2_size_i,
    input  mem_addr_t                       task_scratchpad_3_addr_i,
    input  mem_size_t                       task_scratchpad_3_size_i,
    input  logic                            task_trigger_feedback_i,

    // to pktgen
    input  logic                            feedback_ready_i,
    output logic                            feedback_valid_o,
    output mem_addr_t                       feedback_her_addr_o,
    output mem_size_t                       feedback_her_size_o,
    output logic [C_MSGID_WIDTH-1:0]        feedback_msgid_o,
    output logic                            feedback_trigger_o,

    
    /** NIC outbound engine or NIC command unit **/
    input  logic                            nic_cmd_req_ready_i,
    output logic                            nic_cmd_req_valid_o,
    output pspin_cmd_id_t                   nic_cmd_req_id_o,
    output nid_t                            nic_cmd_req_nid_o,
    output fid_t                            nic_cmd_req_fid_o,
    output host_addr_t                      nic_cmd_req_src_addr_o,
    output mem_size_t                       nic_cmd_req_length_o,
    output user_ptr_t                       nic_cmd_req_user_ptr_o,
    
    input logic                             nic_cmd_resp_valid_i,
    input pspin_cmd_id_t                    nic_cmd_resp_id_i
);

    import pulp_cluster_cfg_pkg::N_TCDM_BANKS;
    import pulp_cluster_cfg_pkg::TCDM_WORDS_PER_BANK;
    import pspin_cfg_pkg::NUM_CLUSTERS;

    import "DPI-C" function string get_slm_path();

/*
    export "DPI-C" function fill_l2_prog_mem;
    export "DPI-C" function fill_l2_handler_mem;
*/
    AXI_BUS #(
        .AXI_ADDR_WIDTH (AXI_AW),
        .AXI_DATA_WIDTH (AXI_WIDE_DW),
        .AXI_ID_WIDTH   (AXI_IW),
        .AXI_USER_WIDTH (AXI_UW)
    ) axi_ni ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH (AXI_AW),
        .AXI_DATA_WIDTH (AXI_WIDE_DW),
        .AXI_ID_WIDTH   (AXI_IW),
        .AXI_USER_WIDTH (AXI_UW)
    ) axi_no ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH (HOST_AXI_AW),
        .AXI_DATA_WIDTH (AXI_WIDE_DW),
        .AXI_ID_WIDTH   (AXI_IW),
        .AXI_USER_WIDTH (AXI_UW)
    ) axi_host_mst ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH (AXI_AW),
        .AXI_DATA_WIDTH (AXI_WIDE_DW),
        .AXI_ID_WIDTH   (AXI_IW),
        .AXI_USER_WIDTH (AXI_UW)
    ) axi_host_slv ();

    logic [pspin_cfg_pkg::NUM_CLUSTERS-1:0] cl_fetch_en;
    logic [pspin_cfg_pkg::NUM_CLUSTERS-1:0] cl_eoc;
    logic [pspin_cfg_pkg::NUM_CLUSTERS-1:0] cl_busy;


    handler_task_t      task_descr;
    feedback_descr_t    feedback;
    pspin_cmd_t         nic_cmd_req;
    pspin_cmd_resp_t    nic_cmd_resp;

    pspin #(
        .N_CLUSTERS           (pspin_cfg_pkg::NUM_CLUSTERS),
        .N_MPQ                (pspin_cfg_pkg::NUM_MPQ)
    ) i_pspin (
        .clk_i                (clk_i),
        .rst_ni               (rst_ni),

        .cl_fetch_en_i        (cl_fetch_en),
        .cl_eoc_o             (cl_eoc),
        .cl_busy_o            (cl_busy),

        .mpq_full_o           (mpq_full_o),

        .axi_ni_slv           (axi_ni),
        .axi_no_slv           (axi_no),
        .axi_host_mst         (axi_host_mst),
        .axi_host_slv         (axi_host_slv),

        .task_ready_o         (task_ready_o),
        .task_valid_i         (task_valid_i),
        .task_i               (task_descr),

        .eos_i                (eos_i),
        .nic_feedback_ready_i (feedback_ready_i),
        .nic_feedback_valid_o (feedback_valid_o),
        .nic_feedback_o       (feedback),
        .pspin_active_o       (pspin_active_o),
        .nic_cmd_ready_i      (nic_cmd_req_ready_i),
        .nic_cmd_valid_o      (nic_cmd_req_valid_o),
        .nic_cmd_o            (nic_cmd_req),
        .nic_cmd_resp_valid_i (nic_cmd_resp_valid_i),
        .nic_cmd_resp_i       (nic_cmd_resp)
    );


    //TODO: move number of rows and number of cols in configuration file!
    for (genvar iRow = 0; iRow < 1; iRow++) begin: gen_fill_l2_hnd_rows
        for (genvar iCol = 0; iCol < 32; iCol++) begin: gen_fill_l2_hnd_cols
            initial begin
                //$readmemh($sformatf("../sim_files/slm_files/l2_hnd_%01d_%01d.slm", iRow, iCol),
                //$display($sformatf(get_l2_handler_slm_path(), iRow, iCol));
                $readmemh({get_slm_path(), $sformatf("l2_hnd_%01d_%01d.slm", iRow, iCol)},
                i_pspin.i_l2_hnd_mem.gen_cols[iCol].gen_rows[iRow].i_mem_cut.i_tc_sram.sram);
            end
        end
    end

    for (genvar iCluster = 0; iCluster < NUM_CLUSTERS; iCluster++) begin: gen_fill_tcdm_cluster
        for (genvar iBank = 0; iBank < N_TCDM_BANKS; iBank++) begin: gen_fill_tcdm_bank
            initial begin
                for (int iWord = 0; iWord < TCDM_WORDS_PER_BANK; iWord++) begin
                    i_pspin.gen_clusters[iCluster].gen_cluster_sync.i_cluster.i_ooc.i_bound.gen_tcdm_banks[iBank].i_mem.i_tc_sram.sram[iWord] = '0;
                end
            end
        end
    end

    initial begin
        //$readmemh("../sim_files/slm_files/prog_mem_stim.slm", i_pspin.i_prog_mem.i_sram.i_tc_sram.sram);
        $readmemh({get_slm_path(), "prog_mem_stim.slm"}, i_pspin.i_prog_mem.i_sram.i_tc_sram.sram);
    end
    
    // // Wait for termination
    // always_ff @(posedge clk_i, negedge rst_ni) begin
    //   if (i_pspin.i_mpq_engine.mpq_busy == '0 && i_pspin.i_mpq_engine.eos_i && i_pspin.i_mpq_engine.fifo_empty) begin
    //     $finish;
    //   end
    // end

    /* enable instruction fetch signal */
    assign cl_fetch_en = (rst_ni) ? 4'b1111 : '0;

    // Connecting axi_ni
    assign axi_ni.aw_addr                           = ni_slave_aw_addr_i;
    assign axi_ni.aw_prot                           = ni_slave_aw_prot_i;
    assign axi_ni.aw_region                         = ni_slave_aw_region_i;
    assign axi_ni.aw_len                            = ni_slave_aw_len_i;
    assign axi_ni.aw_size                           = ni_slave_aw_size_i;
    assign axi_ni.aw_burst                          = ni_slave_aw_burst_i;
    assign axi_ni.aw_lock                           = ni_slave_aw_lock_i;
    assign axi_ni.aw_atop                           = ni_slave_aw_atop_i;
    assign axi_ni.aw_cache                          = ni_slave_aw_cache_i;
    assign axi_ni.aw_qos                            = ni_slave_aw_qos_i;
    assign axi_ni.aw_id                             = ni_slave_aw_id_i;
    assign axi_ni.aw_user                           = ni_slave_aw_user_i;
    assign axi_ni.aw_valid                          = ni_slave_aw_valid_i;
    assign ni_slave_aw_ready_o                      = axi_ni.aw_ready;

    assign axi_ni.ar_addr                           = ni_slave_ar_addr_i;
    assign axi_ni.ar_prot                           = ni_slave_ar_prot_i;
    assign axi_ni.ar_region                         = ni_slave_ar_region_i;
    assign axi_ni.ar_len                            = ni_slave_ar_len_i;
    assign axi_ni.ar_size                           = ni_slave_ar_size_i;
    assign axi_ni.ar_burst                          = ni_slave_ar_burst_i;
    assign axi_ni.ar_lock                           = ni_slave_ar_lock_i;
    assign axi_ni.ar_cache                          = ni_slave_ar_cache_i;
    assign axi_ni.ar_qos                            = ni_slave_ar_qos_i;
    assign axi_ni.ar_id                             = ni_slave_ar_id_i;
    assign axi_ni.ar_user                           = ni_slave_ar_user_i;
    assign axi_ni.ar_valid                          = ni_slave_ar_valid_i;
    assign ni_slave_ar_ready_o                      = axi_ni.ar_ready;

    assign axi_ni.w_data                            = ni_slave_w_data_i;
    assign axi_ni.w_strb                            = ni_slave_w_strb_i;
    assign axi_ni.w_user                            = ni_slave_w_user_i;
    assign axi_ni.w_last                            = ni_slave_w_last_i;
    assign axi_ni.w_valid                           = ni_slave_w_valid_i;
    assign ni_slave_w_ready_o                       = axi_ni.w_ready;

    assign ni_slave_r_data_o                        = axi_ni.r_data;
    assign ni_slave_r_resp_o                        = axi_ni.r_resp;
    assign ni_slave_r_last_o                        = axi_ni.r_last;
    assign ni_slave_r_id_o                          = axi_ni.r_id;
    assign ni_slave_r_user_o                        = axi_ni.r_user;
    assign ni_slave_r_valid_o                       = axi_ni.r_valid;
    assign axi_ni.r_ready                           = ni_slave_r_ready_i;

    assign ni_slave_b_resp_o                        = axi_ni.b_resp;
    assign ni_slave_b_id_o                          = axi_ni.b_id;
    assign ni_slave_b_user_o                        = axi_ni.b_user;
    assign ni_slave_b_valid_o                       = axi_ni.b_valid;
    assign axi_ni.b_ready                           = ni_slave_b_ready_i;


    // Connecting axi_no
    assign axi_no.aw_addr                           = no_slave_aw_addr_i;
    assign axi_no.aw_prot                           = no_slave_aw_prot_i;
    assign axi_no.aw_region                         = no_slave_aw_region_i;
    assign axi_no.aw_len                            = no_slave_aw_len_i;
    assign axi_no.aw_size                           = no_slave_aw_size_i;
    assign axi_no.aw_burst                          = no_slave_aw_burst_i;
    assign axi_no.aw_lock                           = no_slave_aw_lock_i;
    assign axi_no.aw_atop                           = no_slave_aw_atop_i;
    assign axi_no.aw_cache                          = no_slave_aw_cache_i;
    assign axi_no.aw_qos                            = no_slave_aw_qos_i;
    assign axi_no.aw_id                             = no_slave_aw_id_i;
    assign axi_no.aw_user                           = no_slave_aw_user_i;
    assign axi_no.aw_valid                          = no_slave_aw_valid_i;
    assign no_slave_aw_ready_o                      = axi_no.aw_ready;

    assign axi_no.ar_addr                           = no_slave_ar_addr_i;
    assign axi_no.ar_prot                           = no_slave_ar_prot_i;
    assign axi_no.ar_region                         = no_slave_ar_region_i;
    assign axi_no.ar_len                            = no_slave_ar_len_i;
    assign axi_no.ar_size                           = no_slave_ar_size_i;
    assign axi_no.ar_burst                          = no_slave_ar_burst_i;
    assign axi_no.ar_lock                           = no_slave_ar_lock_i;
    assign axi_no.ar_cache                          = no_slave_ar_cache_i;
    assign axi_no.ar_qos                            = no_slave_ar_qos_i;
    assign axi_no.ar_id                             = no_slave_ar_id_i;
    assign axi_no.ar_user                           = no_slave_ar_user_i;
    assign axi_no.ar_valid                          = no_slave_ar_valid_i;
    assign no_slave_ar_ready_o                      = axi_no.ar_ready;

    assign axi_no.w_data                            = no_slave_w_data_i;
    assign axi_no.w_strb                            = no_slave_w_strb_i;
    assign axi_no.w_user                            = no_slave_w_user_i;
    assign axi_no.w_last                            = no_slave_w_last_i;
    assign axi_no.w_valid                           = no_slave_w_valid_i;
    assign no_slave_w_ready_o                       = axi_no.w_ready;

    assign no_slave_r_data_o                        = axi_no.r_data;
    assign no_slave_r_resp_o                        = axi_no.r_resp;
    assign no_slave_r_last_o                        = axi_no.r_last;
    assign no_slave_r_id_o                          = axi_no.r_id;
    assign no_slave_r_user_o                        = axi_no.r_user;
    assign no_slave_r_valid_o                       = axi_no.r_valid;
    assign axi_no.r_ready                           = no_slave_r_ready_i;

    assign no_slave_b_resp_o                        = axi_no.b_resp;
    assign no_slave_b_id_o                          = axi_no.b_id;
    assign no_slave_b_user_o                        = axi_no.b_user;
    assign no_slave_b_valid_o                       = axi_no.b_valid;
    assign axi_no.b_ready                           = no_slave_b_ready_i;


    // Connecting axi_host_slv
    assign axi_host_slv.aw_addr                     = host_slave_aw_addr_i;
    assign axi_host_slv.aw_prot                     = host_slave_aw_prot_i;
    assign axi_host_slv.aw_region                   = host_slave_aw_region_i;
    assign axi_host_slv.aw_len                      = host_slave_aw_len_i;
    assign axi_host_slv.aw_size                     = host_slave_aw_size_i;
    assign axi_host_slv.aw_burst                    = host_slave_aw_burst_i;
    assign axi_host_slv.aw_lock                     = host_slave_aw_lock_i;
    assign axi_host_slv.aw_atop                     = host_slave_aw_atop_i;
    assign axi_host_slv.aw_cache                    = host_slave_aw_cache_i;
    assign axi_host_slv.aw_qos                      = host_slave_aw_qos_i;
    assign axi_host_slv.aw_id                       = host_slave_aw_id_i;
    assign axi_host_slv.aw_user                     = host_slave_aw_user_i;
    assign axi_host_slv.aw_valid                    = host_slave_aw_valid_i;
    assign host_slave_aw_ready_o                    = axi_host_slv.aw_ready;

    assign axi_host_slv.ar_addr                     = host_slave_ar_addr_i;
    assign axi_host_slv.ar_prot                     = host_slave_ar_prot_i;
    assign axi_host_slv.ar_region                   = host_slave_ar_region_i;
    assign axi_host_slv.ar_len                      = host_slave_ar_len_i;
    assign axi_host_slv.ar_size                     = host_slave_ar_size_i;
    assign axi_host_slv.ar_burst                    = host_slave_ar_burst_i;
    assign axi_host_slv.ar_lock                     = host_slave_ar_lock_i;
    assign axi_host_slv.ar_cache                    = host_slave_ar_cache_i;
    assign axi_host_slv.ar_qos                      = host_slave_ar_qos_i;
    assign axi_host_slv.ar_id                       = host_slave_ar_id_i;
    assign axi_host_slv.ar_user                     = host_slave_ar_user_i;
    assign axi_host_slv.ar_valid                    = host_slave_ar_valid_i;
    assign host_slave_ar_ready_o                    = axi_host_slv.ar_ready;

    assign axi_host_slv.w_data                      = host_slave_w_data_i;
    assign axi_host_slv.w_strb                      = host_slave_w_strb_i;
    assign axi_host_slv.w_user                      = host_slave_w_user_i;
    assign axi_host_slv.w_last                      = host_slave_w_last_i;
    assign axi_host_slv.w_valid                     = host_slave_w_valid_i;
    assign host_slave_w_ready_o                     = axi_host_slv.w_ready;

    assign host_slave_r_data_o                      = axi_host_slv.r_data;
    assign host_slave_r_resp_o                      = axi_host_slv.r_resp;
    assign host_slave_r_last_o                      = axi_host_slv.r_last;
    assign host_slave_r_id_o                        = axi_host_slv.r_id;
    assign host_slave_r_user_o                      = axi_host_slv.r_user;
    assign host_slave_r_valid_o                     = axi_host_slv.r_valid;
    assign axi_host_slv.r_ready                     = host_slave_r_ready_i;

    assign host_slave_b_resp_o                      = axi_host_slv.b_resp;
    assign host_slave_b_id_o                        = axi_host_slv.b_id;
    assign host_slave_b_user_o                      = axi_host_slv.b_user;
    assign host_slave_b_valid_o                     = axi_host_slv.b_valid;
    assign axi_host_slv.b_ready                     = host_slave_b_ready_i;

    // Connecting axi_host_mst
    assign host_master_aw_addr_o                    = axi_host_mst.aw_addr;
    assign host_master_aw_prot_o                    = axi_host_mst.aw_prot;
    assign host_master_aw_region_o                  = axi_host_mst.aw_region;
    assign host_master_aw_len_o                     = axi_host_mst.aw_len;
    assign host_master_aw_size_o                    = axi_host_mst.aw_size;
    assign host_master_aw_burst_o                   = axi_host_mst.aw_burst;
    assign host_master_aw_lock_o                    = axi_host_mst.aw_lock;
    assign host_master_aw_atop_o                    = axi_host_mst.aw_atop;
    assign host_master_aw_cache_o                   = axi_host_mst.aw_cache;
    assign host_master_aw_qos_o                     = axi_host_mst.aw_qos;
    assign host_master_aw_id_o                      = axi_host_mst.aw_id;
    assign host_master_aw_user_o                    = axi_host_mst.aw_user;
    assign host_master_aw_valid_o                   = axi_host_mst.aw_valid;
    assign axi_host_mst.aw_ready                    = host_master_aw_ready_i;

    assign host_master_ar_addr_o                    = axi_host_mst.ar_addr;
    assign host_master_ar_prot_o                    = axi_host_mst.ar_prot;
    assign host_master_ar_region_o                  = axi_host_mst.ar_region;
    assign host_master_ar_len_o                     = axi_host_mst.ar_len;
    assign host_master_ar_size_o                    = axi_host_mst.ar_size;
    assign host_master_ar_burst_o                   = axi_host_mst.ar_burst;
    assign host_master_ar_lock_o                    = axi_host_mst.ar_lock;
    assign host_master_ar_cache_o                   = axi_host_mst.ar_cache;
    assign host_master_ar_qos_o                     = axi_host_mst.ar_qos;
    assign host_master_ar_id_o                      = axi_host_mst.ar_id;
    assign host_master_ar_user_o                    = axi_host_mst.ar_user;
    assign host_master_ar_valid_o                   = axi_host_mst.ar_valid;
    assign axi_host_mst.ar_ready                    = host_master_ar_ready_i;

    assign host_master_w_data_o                     = axi_host_mst.w_data;
    assign host_master_w_strb_o                     = axi_host_mst.w_strb;
    assign host_master_w_user_o                     = axi_host_mst.w_user;
    assign host_master_w_last_o                     = axi_host_mst.w_last;
    assign host_master_w_valid_o                    = axi_host_mst.w_valid;
    assign axi_host_mst.w_ready                     = host_master_w_ready_i;

    assign axi_host_mst.r_data                      = host_master_r_data_i;
    assign axi_host_mst.r_resp                      = host_master_r_resp_i;
    assign axi_host_mst.r_last                      = host_master_r_last_i;
    assign axi_host_mst.r_id                        = host_master_r_id_i;
    assign axi_host_mst.r_user                      = host_master_r_user_i;
    assign axi_host_mst.r_valid                     = host_master_r_valid_i;
    assign host_master_r_ready_o                    = axi_host_mst.r_ready;

    assign axi_host_mst.b_resp                      = host_master_b_resp_i; 
    assign axi_host_mst.b_id                        = host_master_b_id_i;
    assign axi_host_mst.b_user                      = host_master_b_user_i;
    assign axi_host_mst.b_valid                     = host_master_b_valid_i;
    assign host_master_b_ready_o                    = axi_host_mst.b_ready;

    // Connecting her_descr
    assign task_descr.msgid                         = task_msgid_i;
    assign task_descr.pkt_addr                      = task_pkt_addr_i;
    assign task_descr.pkt_size                      = task_pkt_size_i;
    assign task_descr.handler_mem_addr              = task_l2_mem_addr_i;
    assign task_descr.handler_mem_size              = task_l2_mem_size_i;
    assign task_descr.host_mem_addr                 = task_host_mem_addr_i;
    assign task_descr.host_mem_size                 = task_host_mem_size_i;
    assign task_descr.handler_fun                   = task_handler_addr_i;
    assign task_descr.handler_fun_size              = task_handler_size_i;
    assign task_descr.scratchpad_addr[0]            = task_scratchpad_0_addr_i;
    assign task_descr.scratchpad_addr[1]            = task_scratchpad_1_addr_i;
    assign task_descr.scratchpad_addr[2]            = task_scratchpad_2_addr_i;
    assign task_descr.scratchpad_addr[3]            = task_scratchpad_3_addr_i;
    assign task_descr.scratchpad_size[0]            = task_scratchpad_0_size_i;
    assign task_descr.scratchpad_size[1]            = task_scratchpad_1_size_i;
    assign task_descr.scratchpad_size[2]            = task_scratchpad_2_size_i;
    assign task_descr.scratchpad_size[3]            = task_scratchpad_3_size_i;
    assign task_descr.trigger_feedback              = task_trigger_feedback_i;
    
    // Connecting feedback
    assign feedback_her_addr_o                      = feedback.pkt_addr;
    assign feedback_her_size_o                      = feedback.pkt_size;
    assign feedback_msgid_o                         = feedback.msgid;
    assign feedback_trigger_o                       = feedback.trigger_feedback;

    // Connecting NIC command request
    assign nic_cmd_req_id_o                         = nic_cmd_req.cmd_id;
    assign nic_cmd_req_nid_o                        = nic_cmd_req.descr.nic_cmd.nid;
    assign nic_cmd_req_fid_o                        = nic_cmd_req.descr.nic_cmd.fid;
    assign nic_cmd_req_src_addr_o                   = nic_cmd_req.descr.nic_cmd.src_addr;
    assign nic_cmd_req_length_o                     = nic_cmd_req.descr.nic_cmd.length;
    assign nic_cmd_req_user_ptr_o                   = nic_cmd_req.descr.nic_cmd.user_ptr;

    // Connecting NIC command response
    assign nic_cmd_resp.cmd_id                      = nic_cmd_resp_id_i; 


  // Observe SoC bus for errors.
  for (genvar iCluster = 0; iCluster < NUM_CLUSTERS; iCluster++) begin: gen_assert_cluster
    assert property (@(posedge i_pspin.clk_i) i_pspin.rst_ni && i_pspin.cl_oup[iCluster].r_valid
        |-> !i_pspin.cl_oup[iCluster].r_resp[1])
      else $warning("R resp error at cl_oup[%01d]", iCluster);

    assert property (@(posedge i_pspin.clk_i) i_pspin.rst_ni && i_pspin.cl_oup[iCluster].b_valid
        |-> !i_pspin.cl_oup[iCluster].b_resp[1])
      else $warning("B resp error at cl_oup[%01d]", iCluster);
  end

endmodule
