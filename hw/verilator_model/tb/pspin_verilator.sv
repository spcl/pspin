// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


package automatic pspin_io;

    typedef logic [pspin_cfg_pkg::AXI_HOST_AW-1:0]    host_addr_t;
    typedef logic [pspin_cfg_pkg::AXI_SOC_AW-1:0]     soc_addr_t;
    typedef logic [pspin_cfg_pkg::AXI_WIDE_DW-1:0]    data_t;
    typedef logic [pspin_cfg_pkg::AXI_WIDE_DW/8-1:0]  strb_t;
    typedef logic [pspin_cfg_pkg::AXI_IW-1:0]         id_t;
    typedef logic [pspin_cfg_pkg::AXI_UW-1:0]         user_t;

endpackage

module pspin_verilator 
  import pspin_cfg_pkg::*;
  import pspin_io::*;
#(
) (
    /** Clocks and Resets **/
    input  logic                            clk_i,
    input  logic                            rst_ni,

    // asserted when HPUs are ready
    output logic                            pspin_active_o,

    // termination signal 
    input  logic                            eos_i,
   
    /** NIC inbound engine AXI slave port **/
    // WRITE ADDRESS CHANNEL
    input  pspin_io::soc_addr_t             ni_slave_aw_addr_i,
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
    input  pspin_io::soc_addr_t             ni_slave_ar_addr_i,
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
    input  pspin_io::soc_addr_t             no_slave_aw_addr_i,
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
    input  pspin_io::soc_addr_t             no_slave_ar_addr_i,
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
    input  pspin_io::soc_addr_t             host_slave_aw_addr_i,
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
    input  pspin_io::soc_addr_t             host_slave_ar_addr_i,
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
    output pspin_io::host_addr_t            host_master_aw_addr_o,
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
    output pspin_io::host_addr_t            host_master_ar_addr_o,
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
    output logic                            her_ready_o,
    input  logic                            her_valid_i,
    input  logic [C_MSGID_WIDTH-1:0]        her_msgid_i,
    input  logic                            her_is_eom_i,
    input  mem_addr_t                       her_addr_i,
    input  mem_size_t                       her_size_i,
    input  mem_size_t                       her_xfer_size_i,
    input  mem_addr_t                       her_meta_handler_mem_addr_i,
    input  mem_size_t                       her_meta_handler_mem_size_i,
    input  host_addr_t                      her_meta_host_mem_addr_i,
    input  mem_size_t                       her_meta_host_mem_size_i,
    input  mem_addr_t                       her_meta_hh_addr_i,
    input  mem_size_t                       her_meta_hh_size_i,
    input  mem_addr_t                       her_meta_ph_addr_i,
    input  mem_size_t                       her_meta_ph_size_i,
    input  mem_addr_t                       her_meta_th_addr_i,
    input  mem_size_t                       her_meta_th_size_i,
    input  mem_addr_t                       her_meta_scratchpad_0_addr_i,
    input  mem_size_t                       her_meta_scratchpad_0_size_i,
    input  mem_addr_t                       her_meta_scratchpad_1_addr_i,
    input  mem_size_t                       her_meta_scratchpad_1_size_i,
    input  mem_addr_t                       her_meta_scratchpad_2_addr_i,
    input  mem_size_t                       her_meta_scratchpad_2_size_i,
    input  mem_addr_t                       her_meta_scratchpad_3_addr_i,
    input  mem_size_t                       her_meta_scratchpad_3_size_i,

    // to pktgen
    input  logic                            feedback_ready_i,
    output logic                            feedback_valid_o,
    output mem_addr_t                       feedback_her_addr_o,
    output mem_size_t                       feedback_her_size_o,
    output logic [C_MSGID_WIDTH-1:0]        feedback_msgid_o,

    
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

    import "DPI-C" function string get_slm_path();

    `AXI_TYPEDEF_ALL( nic_wide, soc_addr_t,  id_t,  data_t,  strb_t,  user_t )
    `AXI_TYPEDEF_ALL( host_out, host_addr_t, id_t,  data_t,  strb_t,  user_t )
    `AXI_TYPEDEF_ALL( host_in,  soc_addr_t,  id_t,  data_t,  strb_t,  user_t )

    host_in_req_t   host_in_req;
    host_in_resp_t  host_in_resp;
    host_out_req_t  host_out_req;
    host_out_resp_t host_out_resp;
    nic_wide_req_t  ni_req, no_req;
    nic_wide_resp_t ni_resp, no_resp;

    her_descr_t         her_descr;
    feedback_descr_t    feedback;
    pspin_cmd_req_t     nic_cmd_req;
    pspin_cmd_resp_t    nic_cmd_resp;

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
        .clk_i                  (clk_i),
        .rst_ni                 (rst_ni),
        
        .host_wide_req_i        (host_in_req),
        .host_wide_resp_o       (host_in_resp),
        .host_wide_req_o        (host_out_req),
        .host_wide_resp_i       (host_out_resp),

        .her_ready_o            (her_ready_o),
        .her_valid_i            (her_valid_i),
        .her_i                  (her_descr),
        .ni_wide_req_i          (ni_req),
        .ni_wide_resp_o         (ni_resp),

        .nic_feedback_ready_i   (feedback_ready),
        .nic_feedback_valid_o   (feedback_valid),
        .nic_feedback_o         (feedback),

        .nic_cmd_ready_i        (nic_cmd_req_ready_i),
        .nic_cmd_valid_o        (nic_cmd_req_valid_o),
        .nic_cmd_o              (nic_cmd_req),

        .nic_cmd_resp_valid_i   (nic_cmd_resp_valid_i),
        .nic_cmd_resp_i         (nic_cmd_resp),
 
        .no_wide_req_i          (no_req),
        .no_wide_resp_o         (no_resp),

        .eos_i                  (eos_i),
        .pspin_active_o         (pspin_active_o)
    );

    //TODO: move number of rows and number of cols in configuration file!
    /*
    for (genvar iRow = 0; iRow < 1; iRow++) begin: gen_fill_l2_hnd_rows
        for (genvar iCol = 0; iCol < L2_HND_N_PAR_CUTS; iCol++) begin: gen_fill_l2_hnd_cols
            initial begin
                //$readmemh($sformatf("../sim_files/slm_files/l2_hnd_%01d_%01d.slm", iRow, iCol),
                //$display($sformatf(get_l2_handler_slm_path(), iRow, iCol));
                $readmemh({get_slm_path(), $sformatf("l2_hnd_%01d_%01d.slm", iRow, iCol)},
                i_pspin.i_l2_hnd_mem.gen_cols[iCol].gen_rows[iRow].i_mem_cut.i_tc_sram.sram);
            end
        end
    end
    */

    /*
    for (genvar iCluster = 0; iCluster < NUM_CLUSTERS; iCluster++) begin: gen_fill_tcdm_cluster
        for (genvar iBank = 0; iBank < L1_NUM_BANKS; iBank++) begin: gen_fill_tcdm_bank
            initial begin
                for (int iWord = 0; iWord < TCDM_WORDS_PER_BANK; iWord++) begin
                    i_pspin.gen_clusters[iCluster].gen_cluster_sync.i_cluster.i_ooc.i_bound.gen_tcdm_banks[iBank].i_mem.i_tc_sram.sram[iWord] = '0;
                end
            end
        end
    end
    */

    initial begin
        $readmemh({get_slm_path(), "prog_mem_stim.slm"}, i_pspin.i_prog_mem.i_sram.i_tc_sram.sram);
    end
    
    // Wait for termination
    always_ff @(posedge clk_i, negedge rst_ni) begin
      if (i_pspin.i_mpq_engine.mpq_busy == '0 && i_pspin.i_mpq_engine.eos_i && i_pspin.i_mpq_engine.fifo_empty) begin
        $finish;
      end
    end

    // Connecting axi_ni
    assign ni_req.aw.addr                           = ni_slave_aw_addr_i;
    assign ni_req.aw.prot                           = ni_slave_aw_prot_i;
    assign ni_req.aw.region                         = ni_slave_aw_region_i;
    assign ni_req.aw.len                            = ni_slave_aw_len_i;
    assign ni_req.aw.size                           = ni_slave_aw_size_i;
    assign ni_req.aw.burst                          = ni_slave_aw_burst_i;
    assign ni_req.aw.lock                           = ni_slave_aw_lock_i;
    assign ni_req.aw.atop                           = ni_slave_aw_atop_i;
    assign ni_req.aw.cache                          = ni_slave_aw_cache_i;
    assign ni_req.aw.qos                            = ni_slave_aw_qos_i;
    assign ni_req.aw.id                             = ni_slave_aw_id_i;
    assign ni_req.aw.user                           = ni_slave_aw_user_i;
    assign ni_req.aw_valid                          = ni_slave_aw_valid_i;
    assign ni_slave_aw_ready_o                      = ni_resp.aw_ready;

    assign ni_req.ar.addr                           = ni_slave_ar_addr_i;
    assign ni_req.ar.prot                           = ni_slave_ar_prot_i;
    assign ni_req.ar.region                         = ni_slave_ar_region_i;
    assign ni_req.ar.len                            = ni_slave_ar_len_i;
    assign ni_req.ar.size                           = ni_slave_ar_size_i;
    assign ni_req.ar.burst                          = ni_slave_ar_burst_i;
    assign ni_req.ar.lock                           = ni_slave_ar_lock_i;
    assign ni_req.ar.cache                          = ni_slave_ar_cache_i;
    assign ni_req.ar.qos                            = ni_slave_ar_qos_i;
    assign ni_req.ar.id                             = ni_slave_ar_id_i;
    assign ni_req.ar.user                           = ni_slave_ar_user_i;
    assign ni_req.ar_valid                          = ni_slave_ar_valid_i;
    assign ni_slave_ar_ready_o                      = ni_resp.ar_ready;

    assign ni_req.w.data                            = ni_slave_w_data_i;
    assign ni_req.w.strb                            = ni_slave_w_strb_i;
    assign ni_req.w.user                            = ni_slave_w_user_i;
    assign ni_req.w.last                            = ni_slave_w_last_i;
    assign ni_req.w_valid                           = ni_slave_w_valid_i;
    assign ni_slave_w_ready_o                       = ni_resp.w_ready;

    assign ni_slave_r_data_o                        = ni_resp.r.data;
    assign ni_slave_r_resp_o                        = ni_resp.r.resp;
    assign ni_slave_r_last_o                        = ni_resp.r.last;
    assign ni_slave_r_id_o                          = ni_resp.r.id;
    assign ni_slave_r_user_o                        = ni_resp.r.user;
    assign ni_slave_r_valid_o                       = ni_resp.r_valid;
    assign ni_req.r_ready                           = ni_slave_r_ready_i;

    assign ni_slave_b_resp_o                        = ni_resp.b.resp;
    assign ni_slave_b_id_o                          = ni_resp.b.id;
    assign ni_slave_b_user_o                        = ni_resp.b.user;
    assign ni_slave_b_valid_o                       = ni_resp.b_valid;
    assign ni_req.b_ready                           = ni_slave_b_ready_i;


    // Connecting axi_no
    assign no_req.aw.addr                           = no_slave_aw_addr_i;
    assign no_req.aw.prot                           = no_slave_aw_prot_i;
    assign no_req.aw.region                         = no_slave_aw_region_i;
    assign no_req.aw.len                            = no_slave_aw_len_i;
    assign no_req.aw.size                           = no_slave_aw_size_i;
    assign no_req.aw.burst                          = no_slave_aw_burst_i;
    assign no_req.aw.lock                           = no_slave_aw_lock_i;
    assign no_req.aw.atop                           = no_slave_aw_atop_i;
    assign no_req.aw.cache                          = no_slave_aw_cache_i;
    assign no_req.aw.qos                            = no_slave_aw_qos_i;
    assign no_req.aw.id                             = no_slave_aw_id_i;
    assign no_req.aw.user                           = no_slave_aw_user_i;
    assign no_req.aw_valid                          = no_slave_aw_valid_i;
    assign no_slave_aw_ready_o                      = no_resp.aw_ready;

    assign no_req.ar.addr                           = no_slave_ar_addr_i;
    assign no_req.ar.prot                           = no_slave_ar_prot_i;
    assign no_req.ar.region                         = no_slave_ar_region_i;
    assign no_req.ar.len                            = no_slave_ar_len_i;
    assign no_req.ar.size                           = no_slave_ar_size_i;
    assign no_req.ar.burst                          = no_slave_ar_burst_i;
    assign no_req.ar.lock                           = no_slave_ar_lock_i;
    assign no_req.ar.cache                          = no_slave_ar_cache_i;
    assign no_req.ar.qos                            = no_slave_ar_qos_i;
    assign no_req.ar.id                             = no_slave_ar_id_i;
    assign no_req.ar.user                           = no_slave_ar_user_i;
    assign no_req.ar_valid                          = no_slave_ar_valid_i;
    assign no_slave_ar_ready_o                      = no_resp.ar_ready;

    assign no_req.w.data                            = no_slave_w_data_i;
    assign no_req.w.strb                            = no_slave_w_strb_i;
    assign no_req.w.user                            = no_slave_w_user_i;
    assign no_req.w.last                            = no_slave_w_last_i;
    assign no_req.w_valid                           = no_slave_w_valid_i;
    assign no_slave_w_ready_o                       = no_resp.w_ready;

    assign no_slave_r_data_o                        = no_resp.r.data;
    assign no_slave_r_resp_o                        = no_resp.r.resp;
    assign no_slave_r_last_o                        = no_resp.r.last;
    assign no_slave_r_id_o                          = no_resp.r.id;
    assign no_slave_r_user_o                        = no_resp.r.user;
    assign no_slave_r_valid_o                       = no_resp.r_valid;
    assign no_req.r_ready                           = no_slave_r_ready_i;

    assign no_slave_b_resp_o                        = no_resp.b.resp;
    assign no_slave_b_id_o                          = no_resp.b.id;
    assign no_slave_b_user_o                        = no_resp.b.user;
    assign no_slave_b_valid_o                       = no_resp.b_valid;
    assign no_req.b_ready                           = no_slave_b_ready_i;


    // Connecting axi_host_slv
    assign host_in_req.aw.addr                      = host_slave_aw_addr_i;
    assign host_in_req.aw.prot                      = host_slave_aw_prot_i;
    assign host_in_req.aw.region                    = host_slave_aw_region_i;
    assign host_in_req.aw.len                       = host_slave_aw_len_i;
    assign host_in_req.aw.size                      = host_slave_aw_size_i;
    assign host_in_req.aw.burst                     = host_slave_aw_burst_i;
    assign host_in_req.aw.lock                      = host_slave_aw_lock_i;
    assign host_in_req.aw.atop                      = host_slave_aw_atop_i;
    assign host_in_req.aw.cache                     = host_slave_aw_cache_i;
    assign host_in_req.aw.qos                       = host_slave_aw_qos_i;
    assign host_in_req.aw.id                        = host_slave_aw_id_i;
    assign host_in_req.aw.user                      = host_slave_aw_user_i;
    assign host_in_req.aw_valid                     = host_slave_aw_valid_i;
    assign host_slave_aw_ready_o                    = host_in_resp.aw_ready;

    assign host_in_req.ar.addr                      = host_slave_ar_addr_i;
    assign host_in_req.ar.prot                      = host_slave_ar_prot_i;
    assign host_in_req.ar.region                    = host_slave_ar_region_i;
    assign host_in_req.ar.len                       = host_slave_ar_len_i;
    assign host_in_req.ar.size                      = host_slave_ar_size_i;
    assign host_in_req.ar.burst                     = host_slave_ar_burst_i;
    assign host_in_req.ar.lock                      = host_slave_ar_lock_i;
    assign host_in_req.ar.cache                     = host_slave_ar_cache_i;
    assign host_in_req.ar.qos                       = host_slave_ar_qos_i;
    assign host_in_req.ar.id                        = host_slave_ar_id_i;
    assign host_in_req.ar.user                      = host_slave_ar_user_i;
    assign host_in_req.ar_valid                     = host_slave_ar_valid_i;
    assign host_slave_ar_ready_o                    = host_in_resp.ar_ready;

    assign host_in_req.w.data                       = host_slave_w_data_i;
    assign host_in_req.w.strb                       = host_slave_w_strb_i;
    assign host_in_req.w.user                       = host_slave_w_user_i;
    assign host_in_req.w.last                       = host_slave_w_last_i;
    assign host_in_req.w_valid                      = host_slave_w_valid_i;
    assign host_slave_w_ready_o                     = host_in_resp.w_ready;

    assign host_slave_r_data_o                      = host_in_resp.r.data;
    assign host_slave_r_resp_o                      = host_in_resp.r.resp;
    assign host_slave_r_last_o                      = host_in_resp.r.last;
    assign host_slave_r_id_o                        = host_in_resp.r.id;
    assign host_slave_r_user_o                      = host_in_resp.r.user;
    assign host_slave_r_valid_o                     = host_in_resp.r_valid;
    assign host_in_req.r_ready                      = host_slave_r_ready_i;

    assign host_slave_b_resp_o                      = host_in_resp.b.resp;
    assign host_slave_b_id_o                        = host_in_resp.b.id;
    assign host_slave_b_user_o                      = host_in_resp.b.user;
    assign host_slave_b_valid_o                     = host_in_resp.b_valid;
    assign host_in_req.b_ready                      = host_slave_b_ready_i;

    // Connecting axi_host_mst
    assign host_master_aw_addr_o                    = host_out_req.aw.addr;
    assign host_master_aw_prot_o                    = host_out_req.aw.prot;
    assign host_master_aw_region_o                  = host_out_req.aw.region;
    assign host_master_aw_len_o                     = host_out_req.aw.len;
    assign host_master_aw_size_o                    = host_out_req.aw.size;
    assign host_master_aw_burst_o                   = host_out_req.aw.burst;
    assign host_master_aw_lock_o                    = host_out_req.aw.lock;
    assign host_master_aw_atop_o                    = host_out_req.aw.atop;
    assign host_master_aw_cache_o                   = host_out_req.aw.cache;
    assign host_master_aw_qos_o                     = host_out_req.aw.qos;
    assign host_master_aw_id_o                      = host_out_req.aw.id;
    assign host_master_aw_user_o                    = host_out_req.aw.user;
    assign host_master_aw_valid_o                   = host_out_req.aw_valid;
    assign host_out_resp.aw_ready                   = host_master_aw_ready_i;

    assign host_master_ar_addr_o                    = host_out_req.ar.addr;
    assign host_master_ar_prot_o                    = host_out_req.ar.prot;
    assign host_master_ar_region_o                  = host_out_req.ar.region;
    assign host_master_ar_len_o                     = host_out_req.ar.len;
    assign host_master_ar_size_o                    = host_out_req.ar.size;
    assign host_master_ar_burst_o                   = host_out_req.ar.burst;
    assign host_master_ar_lock_o                    = host_out_req.ar.lock;
    assign host_master_ar_cache_o                   = host_out_req.ar.cache;
    assign host_master_ar_qos_o                     = host_out_req.ar.qos;
    assign host_master_ar_id_o                      = host_out_req.ar.id;
    assign host_master_ar_user_o                    = host_out_req.ar.user;
    assign host_master_ar_valid_o                   = host_out_req.ar_valid;
    assign host_out_resp.ar_ready                   = host_master_ar_ready_i;

    assign host_master_w_data_o                     = host_out_req.w.data;
    assign host_master_w_strb_o                     = host_out_req.w.strb;
    assign host_master_w_user_o                     = host_out_req.w.user;
    assign host_master_w_last_o                     = host_out_req.w.last;
    assign host_master_w_valid_o                    = host_out_req.w_valid;
    assign host_out_resp.w_ready                    = host_master_w_ready_i;

    assign host_out_resp.r.data                     = host_master_r_data_i;
    assign host_out_resp.r.resp                     = host_master_r_resp_i;
    assign host_out_resp.r.last                     = host_master_r_last_i;
    assign host_out_resp.r.id                       = host_master_r_id_i;
    assign host_out_resp.r.user                     = host_master_r_user_i;
    assign host_out_resp.r_valid                    = host_master_r_valid_i;
    assign host_master_r_ready_o                    = host_out_req.r_ready;

    assign host_out_resp.b.resp                     = host_master_b_resp_i; 
    assign host_out_resp.b.id                       = host_master_b_id_i;
    assign host_out_resp.b.user                     = host_master_b_user_i;
    assign host_out_resp.b_valid                    = host_master_b_valid_i;
    assign host_master_b_ready_o                    = host_out_req.b_ready;

    // Connecting her_descr
    assign her_descr.msgid                          = her_msgid_i;
    assign her_descr.eom                            = her_is_eom_i;
    assign her_descr.her_addr                       = her_addr_i;
    assign her_descr.her_size                       = her_size_i;
    assign her_descr.xfer_size                      = her_xfer_size_i;
    assign her_descr.mpq_meta.handler_mem_addr      = her_meta_handler_mem_addr_i;
    assign her_descr.mpq_meta.handler_mem_size      = her_meta_handler_mem_size_i;
    assign her_descr.mpq_meta.host_mem_addr         = her_meta_host_mem_addr_i;
    assign her_descr.mpq_meta.host_mem_size         = her_meta_host_mem_size_i;
    assign her_descr.mpq_meta.hh_addr               = her_meta_hh_addr_i;
    assign her_descr.mpq_meta.hh_size               = her_meta_hh_size_i;
    assign her_descr.mpq_meta.ph_addr               = her_meta_ph_addr_i;
    assign her_descr.mpq_meta.ph_size               = her_meta_ph_size_i;
    assign her_descr.mpq_meta.th_addr               = her_meta_th_addr_i;
    assign her_descr.mpq_meta.th_size               = her_meta_th_size_i;
    assign her_descr.mpq_meta.scratchpad_addr[0]    = her_meta_scratchpad_0_addr_i;
    assign her_descr.mpq_meta.scratchpad_addr[1]    = her_meta_scratchpad_1_addr_i;
    assign her_descr.mpq_meta.scratchpad_addr[2]    = her_meta_scratchpad_2_addr_i;
    assign her_descr.mpq_meta.scratchpad_addr[3]    = her_meta_scratchpad_3_addr_i;
    assign her_descr.mpq_meta.scratchpad_size[0]    = her_meta_scratchpad_0_size_i;
    assign her_descr.mpq_meta.scratchpad_size[1]    = her_meta_scratchpad_1_size_i;
    assign her_descr.mpq_meta.scratchpad_size[2]    = her_meta_scratchpad_2_size_i;
    assign her_descr.mpq_meta.scratchpad_size[3]    = her_meta_scratchpad_3_size_i;
    
    // Connecting feedback
    assign feedback_her_addr_o                      = feedback.pkt_addr;
    assign feedback_her_size_o                      = feedback.pkt_size;
    assign feedback_msgid_o                         = feedback.msgid;

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
  /*
  for (genvar iCluster = 0; iCluster < NUM_CLUSTERS; iCluster++) begin: gen_assert_cluster
    assert property (@(posedge i_pspin.clk_i) i_pspin.rst_ni && i_pspin.cl_narrow_out_req[iCluster].r_valid
        |-> !i_pspin.cl_narrow_out_resp[iCluster].r.error])
      else $warning("R resp error at cl_oup[%01d]", iCluster);

    assert property (@(posedge i_pspin.clk_i) i_pspin.rst_ni && i_pspin.cl_narrow_out_req[iCluster].b_valid
        |-> !i_pspin.cl_narrow_out_resp[iCluster].b.error)
      else $warning("B resp error at cl_oup[%01d]", iCluster);
  end
  */
endmodule
