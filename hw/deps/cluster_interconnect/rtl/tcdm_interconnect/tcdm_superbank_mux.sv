/// Copyright (c) 2020 ETH Zurich, University of Bologna
/// All rights reserved.
///
/// This code is under development and not yet released to the public.
/// Until it is released, the code is under the copyright of ETH Zurich and
/// the University of Bologna, and may contain confidential and/or unpublished
/// work. Any reuse/redistribution is strictly forbidden without written
/// permission from ETH Zurich.
///
/// Description: Mux between the DMA and the interconnect. 1 DMA access
/// occupies N banks.

/// Author: Thomas Benz <tbenz@iis.ee.ethz.ch>

module tcdm_superbank_mux #(

  parameter int unsigned AddrMemWidth      = -1,
  parameter int unsigned BanksPerSuperbank = -1,
  parameter int unsigned DMADataWidth      = -1,
  parameter int unsigned DataWidth         = -1,
  parameter int unsigned AmoWidth          = -1
) (

  input   logic                                                clk_i,
  input   logic                                                rst_i,

  // interconnect side
  input   logic [BanksPerSuperbank-1:0]                        ic_req_i,        // Bank request
  output  logic [BanksPerSuperbank-1:0]                        ic_gnt_o,        // Bank grant
  input   logic [BanksPerSuperbank-1:0][AddrMemWidth-1:0   ]   ic_add_i,        // Address
  input   logic [BanksPerSuperbank-1:0][AmoWidth-1:0       ]   ic_amo_i,        // Atomic Memory Operation
  input   logic [BanksPerSuperbank-1:0]                        ic_wen_i,        // 1: Store, 0: Load
  input   logic [BanksPerSuperbank-1:0][DataWidth-1:0      ]   ic_wdata_i,      // Write data
  input   logic [BanksPerSuperbank-1:0][DataWidth/8-1:0    ]   ic_be_i,         // Byte enable
  output  logic [BanksPerSuperbank-1:0][DataWidth-1:0      ]   ic_rdata_o,      // Read data

  // dma a side
  input   logic                                                dma_a_req_i,     // Bank request
  output  logic                                                dma_a_gnt_o,     // Bank grant
  input   logic                        [AddrMemWidth-1:0   ]   dma_a_add_i,     // Address
  input   logic                        [AmoWidth-1:0       ]   dma_a_amo_i,     // Atomic Memory Operation
  input   logic                                                dma_a_wen_i,     // 1: Store, 0: Load
  input   logic                        [DMADataWidth-1:0   ]   dma_a_wdata_i,   // Write data
  input   logic                        [DMADataWidth/8-1:0 ]   dma_a_be_i,      // Byte enable
  output  logic                        [DMADataWidth-1:0   ]   dma_a_rdata_o,   // Read data

  // dma b side
  input   logic                                                dma_b_req_i,     // Bank request
  output  logic                                                dma_b_gnt_o,     // Bank grant
  input   logic                        [AddrMemWidth-1:0   ]   dma_b_add_i,     // Address
  input   logic                        [AmoWidth-1:0       ]   dma_b_amo_i,     // Atomic Memory Operation
  input   logic                                                dma_b_wen_i,     // 1: Store, 0: Load
  input   logic                        [DMADataWidth-1:0   ]   dma_b_wdata_i,   // Write data
  input   logic                        [DMADataWidth/8-1:0 ]   dma_b_be_i,      // Byte enable
  output  logic                        [DMADataWidth-1:0   ]   dma_b_rdata_o,   // Read data

  // to memory/amo ports
  output  logic [BanksPerSuperbank-1:0]                        amo_req_o,       // Bank request
  input   logic [BanksPerSuperbank-1:0]                        amo_gnt_i,       // Bank grant
  output  logic [BanksPerSuperbank-1:0][AddrMemWidth-1:0]      amo_add_o,       // Address
  output  logic [BanksPerSuperbank-1:0][AmoWidth-1:0    ]      amo_amo_o,       // Atomic Memory Operation
  output  logic [BanksPerSuperbank-1:0]                        amo_wen_o,       // 1: Store, 0: Load
  output  logic [BanksPerSuperbank-1:0][DataWidth-1:0   ]      amo_wdata_o,     // Write data
  output  logic [BanksPerSuperbank-1:0][DataWidth/8-1:0 ]      amo_be_o,        // Byte enable
  input   logic [BanksPerSuperbank-1:0][DataWidth-1:0   ]      amo_rdata_i,     // Read data

  // general inputs
  input   logic                                                sel_dma_a_i,     // 0: use ic port, 1: use dma port
  input   logic                                                sel_dma_b_i      // 0: use ic port, 1: use dma port
);

  typedef struct packed {
    logic [AddrMemWidth-1:0   ] add;
    logic [AmoWidth-1:0       ] amo;
    logic                       wen;
    logic [DMADataWidth-1:0   ] wdata;
    logic [DMADataWidth/8-1:0 ] be;
  } payload_t;

  // arbitrated signals
  logic     dma_rr_req, dma_rr_gnt;
  payload_t dma_payload_a, dma_payload_b, dma_payload_rr;
  logic     dma_port_used;

  // dma active signal
  logic sel_dma;

  // response is always delayed:
  logic sel_dma_q;

  // arbitrate the two DMA ports
  rr_arb_tree #(
    .NumIn    ( 2         ),
    .DataType ( payload_t )
  ) i_rr_arb_tree (
    .clk_i    ( clk_i                            ),
    .rst_ni   ( ~rst_i                           ),
    .flush_i  ( '0                               ),
    .rr_i     ( '0                               ),
    .req_i    ( { dma_a_req_i,   dma_b_req_i }   ),
    .gnt_o    ( { dma_a_gnt_o,   dma_b_gnt_o }   ),
    .data_i   ( { dma_payload_a, dma_payload_b } ),
    .req_o    ( dma_rr_req                       ),
    .gnt_i    ( dma_rr_gnt                       ),
    .data_o   ( dma_payload_rr                   ),
    .idx_o    ( )
  );

  // one of the two DMA ports is active
  assign sel_dma = sel_dma_a_i | sel_dma_b_i;

  // pack a and b ports
  assign dma_payload_a.add   = dma_a_add_i;
  assign dma_payload_a.amo   = dma_a_amo_i;
  assign dma_payload_a.wen   = dma_a_wen_i;
  assign dma_payload_a.wdata = dma_a_wdata_i;
  assign dma_payload_a.be    = dma_a_be_i;

  assign dma_payload_b.add   = dma_b_add_i;
  assign dma_payload_b.amo   = dma_b_amo_i;
  assign dma_payload_b.wen   = dma_b_wen_i;
  assign dma_payload_b.wdata = dma_b_wdata_i;
  assign dma_payload_b.be    = dma_b_be_i;

  // forwards channel DMA to memory.
  always_comb begin : proc_tcdm_mux

    // default -> feed trough ic requests
    ic_gnt_o       = amo_gnt_i;
    amo_req_o      = ic_req_i;
    amo_add_o      = ic_add_i;
    amo_amo_o      = ic_amo_i;
    amo_wen_o      = ic_wen_i;
    amo_wdata_o    = ic_wdata_i;
    amo_be_o       = ic_be_i;

    // tie dma gnt port to 0
    dma_rr_gnt      = 'b0;


    if(sel_dma) begin
      // block access from tcdm
      ic_gnt_o       = 'b0;
      amo_req_o      = {{BanksPerSuperbank}{dma_rr_req}};
      amo_add_o      = {{BanksPerSuperbank}{dma_payload_rr.add}};
      amo_amo_o      = {{BanksPerSuperbank}{dma_payload_rr.amo}};
      amo_wen_o      = {{BanksPerSuperbank}{dma_payload_rr.wen}};
      amo_wdata_o    = dma_payload_rr.wdata;
      amo_be_o       = dma_payload_rr.be;

      // we need permission from all banks
      dma_rr_gnt = 1'b1;
      for(int i = 0; i < BanksPerSuperbank; i++) begin
        dma_rr_gnt    = dma_rr_gnt & amo_gnt_i;
      end
    end
  end

  // backwards channel memory to DMA, this will be one cycle delayed.
  always_comb begin : proc_tcdm_mux_backwards_channel

    // default: get response from DMA
    ic_rdata_o     = amo_rdata_i;
    dma_a_rdata_o = 'b0;
    dma_b_rdata_o = 'b0;

    // dma did last request -> get now the response
    if(sel_dma_q) begin
      ic_rdata_o    = 'b0;
      dma_a_rdata_o = amo_rdata_i;
      dma_b_rdata_o = amo_rdata_i;
    end
  end

  // delay dma accesses by one for the response channel
  always_ff @(posedge clk_i) begin : proc_delay_dma_sel
    if(rst_i) begin
      sel_dma_q <= 1'b0;
    end else begin
      sel_dma_q <= sel_dma;
    end
  end

endmodule : tcdm_superbank_mux
