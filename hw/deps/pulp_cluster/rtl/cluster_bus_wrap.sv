// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/*
 * cluster_bus_wrap.sv
 * Davide Rossi <davide.rossi@unibo.it>
 * Antonio Pullini <pullinia@iis.ee.ethz.ch>
 * Igor Loi <igor.loi@unibo.it>
 * Francesco Conti <fconti@iis.ee.ethz.ch>
 * Andreas Kurth <akurth@iis.ee.ethz.ch>
 */

`include "axi/assign.svh"
`include "axi/typedef.svh"

module cluster_bus_wrap
#(
  parameter NB_CORES         = 4 ,
  parameter AXI_ADDR_WIDTH   = 32,
  parameter AXI_DATA_WIDTH   = 64,
  parameter AXI_ID_IN_WIDTH  = 4 ,
  parameter AXI_ID_OUT_WIDTH = 6 ,
  parameter AXI_USER_WIDTH   = 6
)
(
  input logic       clk_i,
  input logic       rst_ni,
  input logic       test_en_i,
  input logic [5:0] cluster_id_i,

  AXI_BUS.Slave     data_slave,
  AXI_BUS.Slave     dma_slave,
  AXI_BUS.Slave     ext_slave,

  AXI_BUS.Master    tcdm_master,
  AXI_BUS.Master    periph_master,
  AXI_BUS.Master    ext_master
);

  localparam int unsigned NumRules = 2;
  typedef axi_pkg::xbar_rule_32_t xbar_rule_t;
  axi_pkg::xbar_rule_32_t [NumRules-1:0] addr_map;
  logic [31:0] cluster_base_addr;
  assign cluster_base_addr = 32'h1000_0000 + (cluster_id_i << 22);
  assign addr_map = '{
    '{ // TCDM
      start_addr: cluster_base_addr + 24'h00_0000,
      end_addr:   cluster_base_addr + 24'h10_0000,
      idx:        0
    },
    '{ // Peripherals
      start_addr: cluster_base_addr + 24'h20_0000,
      end_addr:   cluster_base_addr + 24'h40_0000,
      idx:        1
    }
  };
  localparam NumMstPorts = 3;
  localparam NumSlvPorts = 3;
  /* verilator lint_off WIDTHCONCAT */
  localparam axi_pkg::xbar_cfg_t XbarCfg = '{
    NoSlvPorts:                    NumSlvPorts,
    NoMstPorts:                    NumMstPorts,
    MaxMstTrans:                            16,
    MaxSlvTrans:                            32,
    FallThrough:                          1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_PORTS,
    AxiIdWidthSlvPorts:        AXI_ID_IN_WIDTH,
    AxiIdUsedSlvPorts:         AXI_ID_IN_WIDTH,
    AxiAddrWidth:               AXI_ADDR_WIDTH,
    AxiDataWidth:               AXI_DATA_WIDTH,
    NoAddrRules:                      NumRules
  };
  /* verilator lint_on WIDTHCONCAT */

  AXI_BUS #(
            .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
            .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
            .AXI_ID_WIDTH  (AXI_ID_OUT_WIDTH),
            .AXI_USER_WIDTH(AXI_USER_WIDTH)
  ) mst_ports [2:0] ();

  AXI_BUS #(
            .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
            .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
            .AXI_ID_WIDTH  (AXI_ID_IN_WIDTH),
            .AXI_USER_WIDTH(AXI_USER_WIDTH)
  ) slv_ports [2:0] ();

  `AXI_ASSIGN (ext_master,    mst_ports[2])
  `AXI_ASSIGN (periph_master, mst_ports[1])
  `AXI_ASSIGN (tcdm_master,   mst_ports[0])

  `AXI_ASSIGN (slv_ports[2], data_slave)
  `AXI_ASSIGN (slv_ports[1], dma_slave)
  `AXI_ASSIGN (slv_ports[0], ext_slave)

  logic [$clog2(NumMstPorts)-1:0] default_mst_port;
  assign default_mst_port = 2; // default to external master
  axi_xbar_intf #(
    .AXI_USER_WIDTH ( AXI_USER_WIDTH  ),
    .Cfg            ( XbarCfg         ),
    .rule_t         ( xbar_rule_t     )
  ) i_axi_xbar (
    .clk_i,
    .rst_ni,
    .test_i                 ( test_en_i                                 ),
    .slv_ports              ( slv_ports                                 ),
    .mst_ports              ( mst_ports                                 ),
    .addr_map_i             ( addr_map                                  ),
    .en_default_mst_port_i  ( '1                                        ),
    .default_mst_port_i     ( {NumSlvPorts{default_mst_port}}           )
  );

endmodule
