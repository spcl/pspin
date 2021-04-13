// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Thomas Benz <tbenz@ethz.ch>

/// soc-level dma

`include "axi/assign.svh"
`include "axi/typedef.svh"

module pspin_soc_dma #(
    /// id width of the DMA AXI Master port
    parameter int unsigned DmaAxiIdWidth    = -1,
    /// data width of the DMA AXI Master port
    parameter int unsigned DmaDataWidth     = -1,
    /// address width of the DMA AXI Master port
    parameter int unsigned DmaAddrWidth     = -1,
    /// user width
    parameter int unsigned DmaUserWidth     = -1,
    /// number of AX requests in-flight
    parameter int unsigned AxiAxReqDepth    = -1,
    /// number of 1D transfers buffered in backend
    parameter int unsigned TfReqFifoDepth   = -1,
    /// data request type
    parameter type axi_req_t                = logic,
    /// data response type
    parameter type axi_res_t                = logic,
    /// transfer descriptor for hw access to DMA
    parameter type transf_descr_t           = logic,
    parameter logic[DmaAddrWidth-1:0] PCIeStartAddr     = '0,
    parameter logic[DmaAddrWidth-1:0] PCIeEndAddr       = '0,
    parameter logic[DmaAddrWidth-1:0] NHIStartAddr      = '0,
    parameter logic[DmaAddrWidth-1:0] NHIEndAddr        = '0
) (
    input  logic             clk_i,
    input  logic             rst_ni,
    /// direct hw port
    input  logic             rx_req_valid_i,
    output logic             rx_req_ready_o,
    input  transf_descr_t    rx_req_i,
    output logic             rx_rsp_valid_o,
    /// direct hw port
    input  logic             tx_req_valid_i,
    output logic             tx_req_ready_o,
    input  transf_descr_t    tx_req_i,
    output logic             tx_rsp_valid_o,
    /// wide AXI pcie ports
    output axi_req_t         pcie_dma_req_o,
    input  axi_res_t         pcie_dma_res_i,
    /// wide AXI nhi ports
    output axi_req_t         nhi_dma_req_o,
    input  axi_res_t         nhi_dma_res_i,
    /// status signal
    output logic [1:0]       idle_o
);

    localparam int unsigned BaseDMAId = 'h10;

    // 1D burst request
    typedef logic [DmaAddrWidth-1 :0] addr_t;
    typedef logic [DmaAxiIdWidth-1:0] axi_id_t;
    typedef struct packed {
        axi_id_t            id;
        addr_t              src, dst, num_bytes;
        axi_pkg::cache_t    cache_src, cache_dst;
        axi_pkg::burst_t    burst_src, burst_dst;
        logic               decouple_rw;
        logic               deburst;
        logic               serialize;
    } burst_req_t;

    // axi definition
    localparam int unsigned DmaAxiIdWidthMst = DmaAxiIdWidth - 1;

    typedef logic [DmaDataWidth-1    :0] data_t;
    typedef logic [DmaAxiIdWidthMst-1:0] id_mst_t;
    typedef logic [DmaAxiIdWidth-1   :0] id_slv_t;
    typedef logic [DmaDataWidth/8-1  :0] strb_t;
    typedef logic [DmaUserWidth-1    :0] user_t;

    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_mst_t, addr_t, id_mst_t, user_t);
    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_slv_t, addr_t, id_slv_t, user_t);
    `AXI_TYPEDEF_W_CHAN_T (w_chan_t, data_t, strb_t, user_t);
    `AXI_TYPEDEF_B_CHAN_T (b_chan_mst_t, id_mst_t, user_t);
    `AXI_TYPEDEF_B_CHAN_T (b_chan_slv_t, id_slv_t, user_t);
    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_mst_t, addr_t, id_mst_t, user_t);
    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_slv_t, addr_t, id_slv_t, user_t);
    `AXI_TYPEDEF_R_CHAN_T (r_chan_mst_t, data_t, id_mst_t, user_t);
    `AXI_TYPEDEF_R_CHAN_T (r_chan_slv_t, data_t, id_slv_t, user_t);
    `AXI_TYPEDEF_REQ_T    (axi_dma_req_mst_t, aw_chan_mst_t, w_chan_t, ar_chan_mst_t);
    `AXI_TYPEDEF_REQ_T    (axi_dma_req_slv_t, aw_chan_slv_t, w_chan_t, ar_chan_slv_t);
    `AXI_TYPEDEF_RESP_T   (axi_dma_resp_mst_t, b_chan_mst_t, r_chan_mst_t);
    `AXI_TYPEDEF_RESP_T   (axi_dma_resp_slv_t, b_chan_slv_t, r_chan_slv_t);

    axi_dma_req_mst_t  axi_dma_tx_req,  axi_dma_rx_req;
    axi_dma_resp_mst_t axi_dma_tx_resp, axi_dma_rx_resp;

    burst_req_t rx_burst_req, tx_burst_req;

    always_comb begin : proc_map_rx_to_1D_burst
        rx_burst_req.id          = BaseDMAId;
        rx_burst_req.src         = rx_req_i.src_addr;
        rx_burst_req.dst         = rx_req_i.dst_addr;
        rx_burst_req.num_bytes   = rx_req_i.num_bytes;
        rx_burst_req.burst_src   = axi_pkg::BURST_INCR;
        rx_burst_req.burst_dst   = axi_pkg::BURST_INCR;
        rx_burst_req.cache_src   = 4'h0;
        rx_burst_req.cache_dst   = 4'h0;
        rx_burst_req.deburst     = rx_req_i.deburst;
        rx_burst_req.decouple_rw = rx_req_i.decouple;
        rx_burst_req.serialize   = rx_req_i.serialize;
    end

    always_comb begin : proc_map_tx_to_1D_burst
        tx_burst_req.id          = BaseDMAId;
        tx_burst_req.src         = tx_req_i.src_addr;
        tx_burst_req.dst         = tx_req_i.dst_addr;
        tx_burst_req.num_bytes   = tx_req_i.num_bytes;
        tx_burst_req.burst_src   = axi_pkg::BURST_INCR;
        tx_burst_req.burst_dst   = axi_pkg::BURST_INCR;
        tx_burst_req.cache_src   = 4'h0;
        tx_burst_req.cache_dst   = 4'h0;
        tx_burst_req.deburst     = tx_req_i.deburst;
        tx_burst_req.decouple_rw = tx_req_i.decouple;
        tx_burst_req.serialize   = tx_req_i.serialize;
    end
    axi_dma_backend #(
        .DataWidth         ( DmaDataWidth        ),
        .AddrWidth         ( DmaAddrWidth        ),
        .IdWidth           ( DmaAxiIdWidthMst    ),
        .AxReqFifoDepth    ( AxiAxReqDepth       ),
        .TransFifoDepth    ( TfReqFifoDepth      ),
        .BufferDepth       ( 3                   ), // minimal number giving full performance
        .axi_req_t         ( axi_dma_req_mst_t   ),
        .axi_res_t         ( axi_dma_resp_mst_t  ),
        .burst_req_t       ( burst_req_t         ),
        .DmaIdWidth        ( 32                  ), // the width of the internal id of the dma engine (debug only)
        .DmaTracing        ( 0                   )
    ) i_rx_dma_backend (
        .clk_i            ( clk_i            ),
        .rst_ni           ( rst_ni           ),
        .dma_id_i         ( BaseDMAId + 0    ),
        .axi_dma_req_o    ( axi_dma_rx_req   ),
        .axi_dma_res_i    ( axi_dma_rx_resp  ),
        .burst_req_i      ( rx_burst_req     ),
        .valid_i          ( rx_req_valid_i   ),
        .ready_o          ( rx_req_ready_o   ),
        .backend_idle_o   ( idle_o [0]       ),
        .trans_complete_o ( rx_rsp_valid_o   )
    );

    axi_dma_backend #(
        .DataWidth         ( DmaDataWidth        ),
        .AddrWidth         ( DmaAddrWidth        ),
        .IdWidth           ( DmaAxiIdWidthMst    ),
        .AxReqFifoDepth    ( AxiAxReqDepth       ),
        .TransFifoDepth    ( TfReqFifoDepth      ),
        .BufferDepth       ( 3                   ), // minimal number giving full performance
        .axi_req_t         ( axi_dma_req_mst_t   ),
        .axi_res_t         ( axi_dma_resp_mst_t  ),
        .burst_req_t       ( burst_req_t         ),
        .DmaIdWidth        ( 32                  ), // the width of the internal id of the dma engine (debug only)
        .DmaTracing        ( 0                   )
    ) i_tx_dma_backend (
        .clk_i            ( clk_i            ),
        .rst_ni           ( rst_ni           ),
        .dma_id_i         ( BaseDMAId + 1    ),
        .axi_dma_req_o    ( axi_dma_tx_req   ),
        .axi_dma_res_i    ( axi_dma_tx_resp  ),
        .burst_req_i      ( tx_burst_req     ),
        .valid_i          ( tx_req_valid_i   ),
        .ready_o          ( tx_req_ready_o   ),
        .backend_idle_o   ( idle_o [1]       ),
        .trans_complete_o ( tx_rsp_valid_o   )
    );

    // include a x-bar to allow full-duplex copy
    localparam int unsigned NumRules = 2;
    localparam int unsigned IdxPcie = 0;
    localparam int unsigned IdxNhi  = 1;

    typedef struct packed {
    int unsigned idx;
    logic [64:0] start_addr;
    logic [64:0] end_addr;
    } xbar_rule_65_t;

    xbar_rule_65_t [NumRules-1:0] addr_map;

    assign addr_map[IdxPcie] = '{
        start_addr: PCIeStartAddr,
        end_addr:   PCIeEndAddr,
        idx:        IdxPcie
    };

    //I'm not being more detailed here because a detailed
    //address map is already in the NHI interconnect
    assign addr_map[IdxNhi] = '{
        start_addr: NHIStartAddr,
        end_addr:   NHIEndAddr,
        idx:        IdxNhi
    };

    localparam NumMstPorts = 2;
    localparam NumSlvPorts = 2;

    /* verilator lint_off WIDTHCONCAT */
    localparam axi_pkg::xbar_cfg_t XbarCfg = '{
        NoSlvPorts:                    NumSlvPorts,
        NoMstPorts:                    NumMstPorts,
        MaxMstTrans:                            16,
        MaxSlvTrans:                            32,
        FallThrough:                          1'b0,
        LatencyMode:        axi_pkg::CUT_ALL_PORTS,
        AxiIdWidthSlvPorts:       DmaAxiIdWidthMst,
        AxiIdUsedSlvPorts:        DmaAxiIdWidthMst,
        AxiAddrWidth:                 DmaAddrWidth,
        AxiDataWidth:                 DmaDataWidth,
        NoAddrRules:                      NumRules
    };
    /* verilator lint_on WIDTHCONCAT */

    axi_xbar #(
        .Cfg              ( XbarCfg                  ),
        .slv_aw_chan_t    ( aw_chan_mst_t            ),
        .mst_aw_chan_t    ( aw_chan_slv_t            ),
        .w_chan_t         ( w_chan_t                 ),
        .slv_b_chan_t     ( b_chan_mst_t             ),
        .mst_b_chan_t     ( b_chan_slv_t             ),
        .slv_ar_chan_t    ( ar_chan_mst_t            ),
        .mst_ar_chan_t    ( ar_chan_slv_t            ),
        .slv_r_chan_t     ( r_chan_mst_t             ),
        .mst_r_chan_t     ( r_chan_slv_t             ),
        .slv_req_t        ( axi_dma_req_mst_t        ),
        .slv_resp_t       ( axi_dma_resp_mst_t       ),
        .mst_req_t        ( axi_dma_req_slv_t        ),
        .mst_resp_t       ( axi_dma_resp_slv_t       ),
        .rule_t           ( xbar_rule_65_t           )
    ) i_soc_dma_xbar (
        .clk_i                  ( clk_i                                  ),
        .rst_ni                 ( rst_ni                                 ),
        .test_i                 ( 1'b0                                   ),
        .slv_ports_req_i        ( '{ axi_dma_rx_req,  axi_dma_tx_req  }  ),
        .slv_ports_resp_o       ( '{ axi_dma_rx_resp, axi_dma_tx_resp }  ),
        .mst_ports_req_o        ( '{ nhi_dma_req_o, pcie_dma_req_o }     ),
        .mst_ports_resp_i       ( '{ nhi_dma_res_i, pcie_dma_res_i }     ),
        .addr_map_i             ( addr_map                               ),
        .en_default_mst_port_i  ( '0                                     ),
        .default_mst_port_i     ( '0                                     )
    );

endmodule : pspin_soc_dma
