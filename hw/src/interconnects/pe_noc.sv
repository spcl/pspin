// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "axi/typedef.svh"

/// On-chip network interconnecting the PEs of all clusters to the L2, the cluster input ports, and
/// the peripherals.
module pe_noc #(
  parameter int unsigned NumClusters = 0,
  parameter int unsigned AddrWidth = 0,
  parameter int unsigned ClDataWidth = 0,
  parameter int unsigned ClOupIdWidth = 0,
  parameter int unsigned ClInpIdWidth = 0,
  parameter int unsigned L2DataWidth = 0,
  parameter int unsigned L2IdWidth = 0,
  parameter int unsigned PeriphDataWidth = 0,
  parameter int unsigned PeriphIdWidth = 0,
  parameter int unsigned UserWidth = 0,
  parameter type cl_oup_req_t = logic,
  parameter type cl_oup_resp_t = logic,
  parameter type cl_inp_req_t = logic,
  parameter type cl_inp_resp_t = logic,
  parameter type l2_req_t = logic,
  parameter type l2_resp_t = logic,
  parameter type periph_req_t = logic,
  parameter type periph_resp_t = logic,
  // Dependent parameters, do not override!
  parameter type addr_t = logic [AddrWidth-1:0]
) (
  input  logic                            clk_i,
  input  logic                            rst_ni,

  input  addr_t        [NumClusters-1:0]  cl_start_addr_i,
  input  addr_t        [NumClusters-1:0]  cl_end_addr_i,
  input  addr_t                           l2_start_addr_i,
  input  addr_t                           l2_end_addr_i,
  input  addr_t                           periph_start_addr_i,
  input  addr_t                           periph_end_addr_i,

  input  cl_oup_req_t  [NumClusters-1:0]  from_cl_req_i,
  output cl_oup_resp_t [NumClusters-1:0]  from_cl_resp_o,

  output cl_inp_req_t  [NumClusters-1:0]  to_cl_req_o,
  input  cl_inp_resp_t [NumClusters-1:0]  to_cl_resp_i,

  output l2_req_t                         l2_req_o,
  input  l2_resp_t                        l2_resp_i,

  output periph_req_t                     periph_req_o,
  input  periph_resp_t                    periph_resp_i
);

  // Types of ports of clusters.
  typedef logic [ClDataWidth-1:0]   cl_data_t;
  typedef logic [ClDataWidth/8-1:0] cl_strb_t;
  typedef logic [ClOupIdWidth-1:0]  cl_oup_id_t;
  typedef logic [ClInpIdWidth-1:0]  cl_inp_id_t;
  typedef logic [UserWidth-1:0]     user_t;
  `AXI_TYPEDEF_AW_CHAN_T(cl_oup_aw_t, addr_t, cl_oup_id_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(cl_inp_aw_t, addr_t, cl_inp_id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(cl_w_t, cl_data_t, cl_strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(cl_oup_b_t, cl_oup_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(cl_inp_b_t, cl_inp_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(cl_oup_ar_t, addr_t, cl_oup_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(cl_inp_ar_t, addr_t, cl_inp_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(cl_oup_r_t, cl_data_t, cl_oup_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(cl_inp_r_t, cl_data_t, cl_inp_id_t, user_t)

  // Types of master ports of crossbar.
  parameter int unsigned XbarOupIdWidth = ClOupIdWidth + cf_math_pkg::idx_width(NumClusters);
  typedef logic [XbarOupIdWidth-1:0] xbar_oup_id_t;
  `AXI_TYPEDEF_AW_CHAN_T(xbar_oup_aw_t, addr_t, xbar_oup_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(xbar_oup_b_t, xbar_oup_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(xbar_oup_ar_t, addr_t, xbar_oup_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(xbar_oup_r_t, cl_data_t, xbar_oup_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(xbar_oup_req_t, xbar_oup_aw_t, cl_w_t, xbar_oup_ar_t)
  `AXI_TYPEDEF_RESP_T(xbar_oup_resp_t, xbar_oup_b_t, xbar_oup_r_t)
  parameter int unsigned NumMstPorts = NumClusters + 2;
  xbar_oup_req_t  [NumMstPorts-1:0] from_xbar_req;
  xbar_oup_resp_t [NumMstPorts-1:0] from_xbar_resp;

  // Address map of crossbar.
  typedef struct packed {
    int unsigned  idx;
    addr_t        start_addr;
    addr_t        end_addr;
  } xbar_rule_t;
  xbar_rule_t [NumMstPorts-1:0] xbar_addr_map;
  for (genvar i = 0; i < NumMstPorts; i++) begin : gen_addr_map
    assign xbar_addr_map[i].idx = unsigned'(i);
    if (i < NumClusters) begin : gen_map_cluster
      assign xbar_addr_map[i].start_addr = cl_start_addr_i[i];
      assign xbar_addr_map[i].end_addr = cl_end_addr_i[i];
    end else if (i == NumClusters) begin : gen_map_l2
      assign xbar_addr_map[i].start_addr = l2_start_addr_i;
      assign xbar_addr_map[i].end_addr = l2_end_addr_i;
    end else begin : gen_map_periph
      assign xbar_addr_map[i].start_addr = periph_start_addr_i;
      assign xbar_addr_map[i].end_addr = periph_end_addr_i;
    end
  end

  // Configuration and instantiation of crossbar.
  /* verilator lint_off WIDTHCONCAT */
  localparam axi_pkg::xbar_cfg_t xbar_cfg = '{
    NoSlvPorts:         NumClusters,
    NoMstPorts:         NumMstPorts,
    MaxMstTrans:        8, // TODO: calibrate
    MaxSlvTrans:        8, // TODO: calibrate
    FallThrough:        1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_PORTS,
    AxiIdWidthSlvPorts: ClOupIdWidth,
    AxiIdUsedSlvPorts:  ClOupIdWidth,
    AxiAddrWidth:       AddrWidth,
    AxiDataWidth:       ClDataWidth,
    NoAddrRules:        NumMstPorts
  };
  /* verilator lint_on WIDTHCONCAT */

  axi_xbar #(
    .Cfg            (xbar_cfg),
    .slv_aw_chan_t  (cl_oup_aw_t),
    .mst_aw_chan_t  (xbar_oup_aw_t),
    .w_chan_t       (cl_w_t),
    .slv_b_chan_t   (cl_oup_b_t),
    .mst_b_chan_t   (xbar_oup_b_t),
    .slv_ar_chan_t  (cl_oup_ar_t),
    .mst_ar_chan_t  (xbar_oup_ar_t),
    .slv_r_chan_t   (cl_oup_r_t),
    .mst_r_chan_t   (xbar_oup_r_t),
    .slv_req_t      (cl_oup_req_t),
    .slv_resp_t     (cl_oup_resp_t),
    .mst_req_t      (xbar_oup_req_t),
    .mst_resp_t     (xbar_oup_resp_t),
    .rule_t         (xbar_rule_t)
  ) i_xbar (
    .clk_i,
    .rst_ni,
    .test_i                 (1'b0),
    .slv_ports_req_i        (from_cl_req_i),
    .slv_ports_resp_o       (from_cl_resp_o),
    .mst_ports_req_o        (from_xbar_req),
    .mst_ports_resp_i       (from_xbar_resp),
    .addr_map_i             (xbar_addr_map),
    .en_default_mst_port_i  ({NumClusters{1'b0}}),
    .default_mst_port_i     ({NumClusters{{$clog2(NumMstPorts){1'b0}}}})
  );

  // ID width converters into clusters.
  for (genvar i = 0; i < NumClusters; i++) begin : gen_cluster_inp_iw_converter
    axi_id_remap #(
      .AxiSlvPortIdWidth    (XbarOupIdWidth),
      .AxiMstPortIdWidth    (ClInpIdWidth),
      .AxiSlvPortMaxUniqIds (8),  // TODO: calibrate
      .AxiMaxTxnsPerId      (2),  // TODO: calibrate (=depth of store buffer?)
      .slv_req_t            (xbar_oup_req_t),
      .slv_resp_t           (xbar_oup_resp_t),
      .mst_req_t            (cl_inp_req_t),
      .mst_resp_t           (cl_inp_resp_t)
    ) i_iw_converter_cl (
      .clk_i,
      .rst_ni,
      .slv_req_i  (from_xbar_req[i]),
      .slv_resp_o (from_xbar_resp[i]),
      .mst_req_o  (to_cl_req_o[i]),
      .mst_resp_i (to_cl_resp_i[i])
    );
  end

  // ID width converter towards L2.
  typedef logic [L2IdWidth-1:0] l2_id_t;
  `AXI_TYPEDEF_AW_CHAN_T(l2_aw_t, addr_t, l2_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(l2_b_t, l2_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(l2_ar_t, addr_t, l2_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(cl_l2_r_t, cl_data_t, l2_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(cl_l2_req_t, l2_aw_t, cl_w_t, l2_ar_t)
  `AXI_TYPEDEF_RESP_T(cl_l2_resp_t, l2_b_t, cl_l2_r_t)
  cl_l2_req_t   cl_l2_req;
  cl_l2_resp_t  cl_l2_resp;
  axi_id_remap #(
    .AxiSlvPortIdWidth    (XbarOupIdWidth),
    .AxiMstPortIdWidth    (L2IdWidth),
    .AxiSlvPortMaxUniqIds (8),  // TODO: calibrate
    .AxiMaxTxnsPerId      (2),  // TODO: calibrate (=depth of store buffer?)
    .slv_req_t            (xbar_oup_req_t),
    .slv_resp_t           (xbar_oup_resp_t),
    .mst_req_t            (cl_l2_req_t),
    .mst_resp_t           (cl_l2_resp_t)
  ) i_iw_converter_l2 (
    .clk_i,
    .rst_ni,
    .slv_req_i  (from_xbar_req[NumClusters]),
    .slv_resp_o (from_xbar_resp[NumClusters]),
    .mst_req_o  (cl_l2_req),
    .mst_resp_i (cl_l2_resp)
  );

  // Data width converter towards L2.
  typedef logic [L2DataWidth-1:0]   l2_data_t;
  typedef logic [L2DataWidth/8-1:0] l2_strb_t;
  `AXI_TYPEDEF_W_CHAN_T(l2_w_t, l2_data_t, l2_strb_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(l2_r_t, l2_data_t, l2_id_t, user_t)
  axi_dw_converter #(
    .AxiMaxReads          (8),  // TODO: calibrate
    .AxiSlvPortDataWidth  (ClDataWidth),
    .AxiMstPortDataWidth  (L2DataWidth),
    .AxiAddrWidth         (AddrWidth),
    .AxiIdWidth           (L2IdWidth),
    .aw_chan_t            (l2_aw_t),
    .slv_w_chan_t         (cl_w_t),
    .mst_w_chan_t         (l2_w_t),
    .b_chan_t             (l2_b_t),
    .ar_chan_t            (l2_ar_t),
    .slv_r_chan_t         (cl_l2_r_t),
    .mst_r_chan_t         (l2_r_t),
    .axi_slv_req_t        (cl_l2_req_t),
    .axi_slv_resp_t       (cl_l2_resp_t),
    .axi_mst_req_t        (l2_req_t),
    .axi_mst_resp_t       (l2_resp_t)
  ) i_dw_converter_l2 (
    .clk_i,
    .rst_ni,
    .slv_req_i  (cl_l2_req),
    .slv_resp_o (cl_l2_resp),
    .mst_req_o  (l2_req_o),
    .mst_resp_i (l2_resp_i)
  );

  // ID width converter towards peripherals.
  typedef logic [PeriphIdWidth-1:0] periph_id_t;
  `AXI_TYPEDEF_AW_CHAN_T(periph_aw_t, addr_t, periph_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(periph_b_t, periph_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(periph_ar_t, addr_t, periph_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(cl_periph_r_t, cl_data_t, periph_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(cl_periph_req_t, periph_aw_t, cl_w_t, periph_ar_t)
  `AXI_TYPEDEF_RESP_T(cl_periph_resp_t, periph_b_t, cl_periph_r_t)
  cl_periph_req_t   cl_periph_req;
  cl_periph_resp_t  cl_periph_resp;
  axi_id_remap #(
    .AxiSlvPortIdWidth    (XbarOupIdWidth),
    .AxiMstPortIdWidth    (PeriphIdWidth),
    .AxiSlvPortMaxUniqIds (4),  // TODO: calibrate
    .AxiMaxTxnsPerId      (1),  // TODO: calibrate
    .slv_req_t            (xbar_oup_req_t),
    .slv_resp_t           (xbar_oup_resp_t),
    .mst_req_t            (cl_periph_req_t),
    .mst_resp_t           (cl_periph_resp_t)
  ) i_iw_converter_periph (
    .clk_i,
    .rst_ni,
    .slv_req_i  (from_xbar_req[NumClusters+1]),
    .slv_resp_o (from_xbar_resp[NumClusters+1]),
    .mst_req_o  (cl_periph_req),
    .mst_resp_i (cl_periph_resp)
  );

  // Data width converter towards peripherals.
  typedef logic [PeriphDataWidth-1:0]   periph_data_t;
  typedef logic [PeriphDataWidth/8-1:0] periph_strb_t;
  `AXI_TYPEDEF_W_CHAN_T(periph_w_t, periph_data_t, periph_strb_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(periph_r_t, periph_data_t, periph_id_t, user_t)
  axi_dw_converter #(
    .AxiMaxReads          (4),  // TODO: calibrate
    .AxiSlvPortDataWidth  (ClDataWidth),
    .AxiMstPortDataWidth  (PeriphDataWidth),
    .AxiAddrWidth         (AddrWidth),
    .AxiIdWidth           (PeriphIdWidth),
    .aw_chan_t            (periph_aw_t),
    .slv_w_chan_t         (cl_w_t),
    .mst_w_chan_t         (periph_w_t),
    .b_chan_t             (periph_b_t),
    .ar_chan_t            (periph_ar_t),
    .slv_r_chan_t         (cl_periph_r_t),
    .mst_r_chan_t         (periph_r_t),
    .axi_slv_req_t        (cl_periph_req_t),
    .axi_slv_resp_t       (cl_periph_resp_t),
    .axi_mst_req_t        (periph_req_t),
    .axi_mst_resp_t       (periph_resp_t)
  ) i_dw_converter_periph (
    .clk_i,
    .rst_ni,
    .slv_req_i  (cl_periph_req),
    .slv_resp_o (cl_periph_resp),
    .mst_req_o  (periph_req_o),
    .mst_resp_i (periph_resp_i)
  );

endmodule
