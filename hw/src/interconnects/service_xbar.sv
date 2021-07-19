// Copyright (c) 2021 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "axi/typedef.svh"

module service_xbar #(
  parameter int unsigned NumClusters = 0,
  parameter int unsigned AddrWidth = 0,
  parameter int unsigned ServiceIDWidth = 0,
  parameter int unsigned ServiceDataWidth = 0,
  parameter int unsigned L2ProgDataWidth = 0,
  parameter int unsigned L2ProgIdWidth = 0,
  parameter int unsigned L2DataDataWidth = 0,
  parameter int unsigned L2DataIdWidth = 0,
  parameter int unsigned UserWidth = 0,
  parameter type service_req_t = logic,
  parameter type service_rsp_t = logic,
  parameter type icache_req_t = logic,
  parameter type icache_rsp_t = logic,
  parameter type ptw_req_t = logic,
  parameter type ptw_rsp_t = logic,
  // Dependent parameters, do not override!
  parameter type addr_t = logic [AddrWidth-1:0]
) (
    input  logic                           clk_i,
    input  logic                           rst_ni,

    // service slv ports
    input  service_req_t [NumClusters-1:0] service_req_i,
    output service_rsp_t [NumClusters-1:0] service_rsp_o,

    // icache mst port
    output icache_req_t                    icache_req_o,
    input  icache_rsp_t                    icache_rsp_i,

    // data mst port (PTW)
    output ptw_req_t                       ptw_req_o,
    input  ptw_rsp_t                       ptw_rsp_i,

    // L2 data (handler + pkt) addresses
    input  addr_t                          l2d_start_addr_i,
    input  addr_t                          l2d_end_addr_i,

    // L2 prog addresses
    input  addr_t                          l2i_start_addr_i,
    input  addr_t                          l2i_end_addr_i
);
    // icache and mem (for the PTW)
    localparam int unsigned NumMstPorts = 2;

    // Address map of crossbar.
    typedef struct packed {
        int unsigned  idx;
        addr_t        start_addr;
        addr_t        end_addr;
    } xbar_rule_t;
    
    xbar_rule_t [NumMstPorts-1:0] xbar_addr_map;

    // Service ports types.
    typedef logic [ServiceDataWidth-1:0]   service_data_t;
    typedef logic [ServiceDataWidth/8-1:0] service_strb_t;
    typedef logic [ServiceIDWidth-1:0]     service_id_t;
    typedef logic [UserWidth-1:0]          service_user_t;
    `AXI_TYPEDEF_ALL(service_slv, addr_t, service_id_t, service_data_t, service_strb_t, service_user_t)

    // Types of master ports of crossbar.
    parameter int unsigned XbarOupIdWidth = ServiceIDWidth + cf_math_pkg::idx_width(NumClusters);
    typedef logic [XbarOupIdWidth-1:0] xbar_mst_id_t;
    `AXI_TYPEDEF_ALL(xbar_mst, addr_t, xbar_mst_id_t, service_data_t, service_strb_t, service_user_t)

    xbar_mst_req_t  xbar_icache_req, xbar_ptw_req;
    xbar_mst_resp_t xbar_icache_rsp, xbar_ptw_rsp;
    
    assign xbar_addr_map[0].idx = 0;
    assign xbar_addr_map[0].start_addr = l2i_start_addr_i;
    assign xbar_addr_map[0].end_addr = l2i_end_addr_i;

    assign xbar_addr_map[1].idx = 1;
    assign xbar_addr_map[1].start_addr = l2d_start_addr_i;
    assign xbar_addr_map[1].end_addr = l2d_end_addr_i;

    // Configuration and instantiation of crossbar.
    /* verilator lint_off WIDTHCONCAT */
    localparam axi_pkg::xbar_cfg_t xbar_cfg = '{
        NoSlvPorts:         NumClusters,
        NoMstPorts:         NumMstPorts,
        MaxMstTrans:        8, // TODO: calibrate
        MaxSlvTrans:        8, // TODO: calibrate
        FallThrough:        1'b0,
        LatencyMode:        axi_pkg::CUT_ALL_PORTS,
        AxiIdWidthSlvPorts: ServiceIDWidth,
        AxiIdUsedSlvPorts:  ServiceIDWidth,
        AxiAddrWidth:       AddrWidth,
        AxiDataWidth:       ServiceDataWidth,
        NoAddrRules:        NumMstPorts
    };
    /* verilator lint_on WIDTHCONCAT */

    axi_xbar #(
        .Cfg            (xbar_cfg),
        .slv_aw_chan_t  (service_slv_aw_chan_t),
        .mst_aw_chan_t  (xbar_mst_aw_chan_t),
        .w_chan_t       (service_slv_w_chan_t),
        .slv_b_chan_t   (service_slv_b_chan_t),
        .mst_b_chan_t   (xbar_mst_b_chan_t),
        .slv_ar_chan_t  (service_slv_ar_chan_t),
        .mst_ar_chan_t  (xbar_mst_ar_chan_t),
        .slv_r_chan_t   (service_slv_r_chan_t),
        .mst_r_chan_t   (xbar_mst_r_chan_t),
        .slv_req_t      (service_slv_req_t),
        .slv_resp_t     (service_slv_resp_t),
        .mst_req_t      (xbar_mst_req_t),
        .mst_resp_t     (xbar_mst_resp_t),
        .rule_t         (xbar_rule_t)
    ) i_xbar (
        .clk_i,
        .rst_ni,
        .test_i                 (1'b0),
        .slv_ports_req_i        (service_req_i),
        .slv_ports_resp_o       (service_rsp_o),
        .mst_ports_req_o        ({xbar_ptw_req, xbar_icache_req}),
        .mst_ports_resp_i       ({xbar_ptw_rsp, xbar_icache_rsp}),
        .addr_map_i             (xbar_addr_map),
        .en_default_mst_port_i  ({NumClusters{1'b0}}),
        .default_mst_port_i     ({NumClusters{{$clog2(NumMstPorts){1'b0}}}})
    );

    // ID width converter towards L2 data and prog.
    typedef logic [L2DataIdWidth-1:0] l2d_id_t;
    `AXI_TYPEDEF_ALL(cl_l2d, addr_t, l2d_id_t, service_data_t, service_strb_t, service_user_t)

    cl_l2d_req_t   cl_l2d_req;
    cl_l2d_resp_t  cl_l2d_resp;
    
    axi_id_remap #(
        .AxiSlvPortIdWidth    (XbarOupIdWidth),
        .AxiMstPortIdWidth    (L2DataIdWidth),
        .AxiSlvPortMaxUniqIds (8),  // TODO: calibrate
        .AxiMaxTxnsPerId      (2),  // TODO: calibrate (=depth of store buffer?)
        .slv_req_t            (xbar_mst_req_t),
        .slv_resp_t           (xbar_mst_resp_t),
        .mst_req_t            (cl_l2d_req_t),
        .mst_resp_t           (cl_l2d_resp_t)
    ) i_iw_converter_l2d (
        .clk_i,
        .rst_ni,
        .slv_req_i  (xbar_ptw_req),
        .slv_resp_o (xbar_ptw_rsp),
        .mst_req_o  (cl_l2d_req),
        .mst_resp_i (cl_l2d_resp)
    );

    // Data width converter towards L2 data.
    typedef logic [L2DataDataWidth-1:0]   l2d_data_t;
    typedef logic [L2DataDataWidth/8-1:0] l2d_strb_t;
    `AXI_TYPEDEF_W_CHAN_T(l2d_w_chan_t, l2d_data_t, l2d_strb_t, service_user_t)
    `AXI_TYPEDEF_R_CHAN_T(l2d_r_chan_t, l2d_data_t, l2d_id_t, service_user_t)
    axi_dw_converter #(
        .AxiMaxReads          (8),  // TODO: calibrate
        .AxiSlvPortDataWidth  (ServiceDataWidth),
        .AxiMstPortDataWidth  (L2DataDataWidth),
        .AxiAddrWidth         (AddrWidth),
        .AxiIdWidth           (L2DataIdWidth),
        .aw_chan_t            (cl_l2d_aw_chan_t),
        .slv_w_chan_t         (cl_l2d_w_chan_t),
        .mst_w_chan_t         (l2d_w_chan_t),
        .b_chan_t             (cl_l2d_b_chan_t),
        .ar_chan_t            (cl_l2d_ar_chan_t),
        .slv_r_chan_t         (cl_l2d_r_chan_t),
        .mst_r_chan_t         (l2d_r_chan_t),
        .axi_slv_req_t        (cl_l2d_req_t),
        .axi_slv_resp_t       (cl_l2d_resp_t),
        .axi_mst_req_t        (ptw_req_t),
        .axi_mst_resp_t       (ptw_rsp_t)
    ) i_dw_converter_l2d (
        .clk_i,
        .rst_ni,
        .slv_req_i  (cl_l2d_req),
        .slv_resp_o (cl_l2d_resp),
        .mst_req_o  (ptw_req_o),
        .mst_resp_i (ptw_rsp_o)
    );

    // ID width converter towards L2 prog.
    typedef logic [L2ProgIdWidth-1:0] l2i_id_t;
    `AXI_TYPEDEF_ALL(cl_l2i, addr_t, l2i_id_t, service_data_t, service_strb_t, service_user_t)

    cl_l2i_req_t   cl_l2i_req;
    cl_l2i_resp_t  cl_l2i_resp;

    axi_id_remap #(
        .AxiSlvPortIdWidth    (XbarOupIdWidth),
        .AxiMstPortIdWidth    (L2ProgIdWidth),
        .AxiSlvPortMaxUniqIds (8),  // TODO: calibrate
        .AxiMaxTxnsPerId      (2),  // TODO: calibrate (=depth of store buffer?)
        .slv_req_t            (xbar_mst_req_t),
        .slv_resp_t           (xbar_mst_resp_t),
        .mst_req_t            (cl_l2i_req_t),
        .mst_resp_t           (cl_l2i_resp_t)
    ) i_iw_converter_l2i (
        .clk_i,
        .rst_ni,
        .slv_req_i  (xbar_icache_req),
        .slv_resp_o (xbar_icache_rsp),
        .mst_req_o  (cl_l2i_req),
        .mst_resp_i (cl_l2i_resp)
    );

    // Data width converter towards L2 prog.
    typedef logic [L2ProgDataWidth-1:0]   l2i_data_t;
    typedef logic [L2ProgDataWidth/8-1:0] l2i_strb_t;
    `AXI_TYPEDEF_W_CHAN_T(l2i_w_chan_t, l2i_data_t, l2i_strb_t, service_user_t)
    `AXI_TYPEDEF_R_CHAN_T(l2i_r_chan_t, l2i_data_t, l2i_id_t, service_user_t)

    axi_dw_converter #(
        .AxiMaxReads          (8),  // TODO: calibrate
        .AxiSlvPortDataWidth  (ServiceDataWidth),
        .AxiMstPortDataWidth  (L2ProgDataWidth),
        .AxiAddrWidth         (AddrWidth),
        .AxiIdWidth           (L2ProgIdWidth),
        .aw_chan_t            (cl_l2i_aw_chan_t),
        .slv_w_chan_t         (cl_l2i_w_chan_t),
        .mst_w_chan_t         (l2i_w_chan_t),
        .b_chan_t             (cl_l2i_b_chan_t),
        .ar_chan_t            (cl_l2i_ar_chan_t),
        .slv_r_chan_t         (cl_l2i_r_chan_t),
        .mst_r_chan_t         (l2i_r_chan_t),
        .axi_slv_req_t        (cl_l2i_req_t),
        .axi_slv_resp_t       (cl_l2i_resp_t),
        .axi_mst_req_t        (icache_req_t),
        .axi_mst_resp_t       (icache_rsp_t)
    ) i_dw_converter_l2i (
        .clk_i,
        .rst_ni,
        .slv_req_i  (cl_l2i_req),
        .slv_resp_o (cl_l2i_resp),
        .mst_req_o  (icache_req_o),
        .mst_resp_i (icache_rsp_o)
    );

endmodule