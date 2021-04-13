// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// this does not work if we are pushing and popping at the same time
// from a queue of size 0
module fifo_engine #(
    //dynamic cells
    parameter int NUM_CELLS = 64,
    parameter int NUM_FIFO  = 16,
    parameter int NUM_STATIC_CELLS_PER_FIFO = 4,
    parameter type elem_t = logic,
    
    //do not touch!
    parameter int TOT_STATIC_CELLS = NUM_STATIC_CELLS_PER_FIFO * NUM_FIFO,
    parameter int TOT_CELLS = TOT_STATIC_CELLS + NUM_CELLS,
    parameter type fifo_id_t = logic [$clog2(NUM_FIFO)-1:0],
    parameter type cell_id_t = logic [$clog2(TOT_CELLS)-1:0]
) (
    input  logic                 clk_i,
    input  logic                 rst_ni,

    //push interface
    input  elem_t                new_el_i,
    input  logic                 push_i,
    input  fifo_id_t             fifo_push_id_i,

    //pop interface
    input  logic                 pop_i,
    input  fifo_id_t             fifo_pop_id_i,
    output elem_t                data_o, 

    //output interface
    output logic                 empty_o,
    output logic [NUM_FIFO-1:0]  fifo_full_o
);

    typedef struct packed {
        cell_id_t next;
        logic is_last;
    } cell_t;

    localparam int unsigned ELEM_SIZE   = $bits(elem_t);
    localparam int unsigned ELEM_SIZE_B = $bits(elem_t)/8;

    cell_t [TOT_CELLS-1:0] cells_q;
    cell_t [TOT_CELLS-1:0] cells_d;

    logic [TOT_CELLS-1:0] free_cells_d;
    logic [TOT_CELLS-1:0] free_cells_q;

    cell_id_t [NUM_FIFO-1:0] fifo_head_d;
    cell_id_t [NUM_FIFO-1:0] fifo_head_q;

    cell_id_t [NUM_FIFO-1:0] fifo_last_d;
    cell_id_t [NUM_FIFO-1:0] fifo_last_q;

    logic [NUM_FIFO-1:0] fifo_empty_q;
    logic [NUM_FIFO-1:0] fifo_empty_d;

    logic [NUM_FIFO-1:0][$clog2(NUM_STATIC_CELLS_PER_FIFO):0] fifo_static_occup_q;
    logic [NUM_FIFO-1:0][$clog2(NUM_STATIC_CELLS_PER_FIFO):0] fifo_static_occup_d;

    cell_id_t free_dynamic_cell_idx;
    cell_id_t free_static_cell_idx, free_static_cell_idx_lzc;
    cell_id_t push_cell_idx, pop_cell_idx;
    logic no_free_dynamic_cells, no_free_static_cells;
    logic pushing_to_static;
    logic popping_from_static;

    // free dynamic slots
    assign free_dynamic_cell_idx[$clog2(TOT_CELLS)-1:$clog2(NUM_CELLS)] = '0;
    lzc #(
        .WIDTH  (NUM_CELLS)
    ) i_lzc_dynamic_free_slots (
        .in_i    (~(free_cells_q[NUM_CELLS-1:0])),
        .cnt_o   (free_dynamic_cell_idx[$clog2(NUM_CELLS)-1:0]),
        .empty_o (no_free_dynamic_cells)
    );

    // free static slots
    assign free_static_cell_idx = free_static_cell_idx_lzc + NUM_CELLS;
    assign free_static_cell_idx_lzc[$clog2(TOT_CELLS)-1:$clog2(TOT_STATIC_CELLS)] = '0;
    lzc #(
        .WIDTH  (TOT_STATIC_CELLS)
    ) i_lzc_static_free_slots (
        .in_i    (~(free_cells_q[TOT_CELLS-1:NUM_CELLS])),
        .cnt_o   (free_static_cell_idx_lzc[$clog2(TOT_STATIC_CELLS)-1:0]),
        .empty_o (no_free_static_cells)
    );

    //memory for storing FIFO entries
    elem_t fifo_data_ignored;
    tc_sram #(
        .NumWords   (TOT_CELLS),
        .DataWidth  (ELEM_SIZE),
        .NumPorts   (2)
    ) i_fifo_data (
        .clk_i      (clk_i),
        .rst_ni     (rst_ni),
        .req_i      ({push_i, 1'b1}),
        .we_i       ({push_i, 1'b0}),
        .addr_i     ({push_cell_idx, pop_cell_idx}),
        .wdata_i    ({new_el_i, {ELEM_SIZE{1'b0}}}),
        .be_i       ({{ELEM_SIZE_B{1'b1}}, {ELEM_SIZE_B{1'b0}}}),
        .rdata_o    ({fifo_data_ignored, data_o})
    );

    //output 
    assign empty_o = (free_cells_q == '0);  
    
    for (genvar i=0; i<NUM_FIFO; i++) begin
        assign fifo_full_o[i] = no_free_dynamic_cells && (fifo_static_occup_q[i] == NUM_STATIC_CELLS_PER_FIFO);
    end

    //occupation
    //here, by using fifo_static_occup_q, we are allowing that an element is pushed to a dynamic
    //cell even if there is a static one that just freed up (pop in the same cycle on the same fifo).
    //This should not be a big issue because, if we get push, we assume that the pusher chekes
    //that !fifo_full[i] (where i is the fifo where we are pushing too). If this assumption holds,
    //the push succeeds even if it goes to a dynamic cell. 
    assign pushing_to_static = (fifo_static_occup_q[fifo_push_id_i] < NUM_STATIC_CELLS_PER_FIFO); 
    assign push_cell_idx = (pushing_to_static) ? free_static_cell_idx : free_dynamic_cell_idx;
    assign popping_from_static = (fifo_head_q[fifo_pop_id_i] >= NUM_CELLS);

    assign pop_cell_idx = fifo_head_q[fifo_pop_id_i];

    always_comb begin
        free_cells_d = free_cells_q;

        if (push_i) begin
            free_cells_d[push_cell_idx] = 1'b1;
        end

        if (pop_i) begin
            free_cells_d[fifo_head_q[fifo_pop_id_i]] = 1'b0;
        end
    end

    //static cells occupation
    always_comb begin
        fifo_static_occup_d = fifo_static_occup_q;

        if (push_i && pop_i && fifo_push_id_i == fifo_pop_id_i) begin
            //special case: we are pushing and popping from the same MPQ
            case ({pushing_to_static, popping_from_static}) 
                2'b10: fifo_static_occup_d[fifo_push_id_i] = fifo_static_occup_q[fifo_push_id_i] + 1;
                2'b01: fifo_static_occup_d[fifo_push_id_i] = fifo_static_occup_q[fifo_push_id_i] - 1; 
            endcase
        end else begin
            //we are popping/pushing on different MPQs or we are either popping or pushing
            //to the same MPQ. 
            if (push_i && pushing_to_static) begin
                fifo_static_occup_d[fifo_push_id_i] = fifo_static_occup_q[fifo_push_id_i] + 1;
            end

            if (pop_i && popping_from_static) begin
                fifo_static_occup_d[fifo_pop_id_i] = fifo_static_occup_q[fifo_pop_id_i] - 1;
            end
        end
    end

    //pointers
    always_comb begin
        fifo_last_d = fifo_last_q;
        fifo_head_d = fifo_head_q;
        cells_d = cells_q;
        fifo_empty_d = fifo_empty_q;

        if (push_i && pop_i && fifo_push_id_i == fifo_pop_id_i && cells_q[fifo_head_q[fifo_push_id_i]].is_last) begin
            fifo_head_d[fifo_pop_id_i] = push_cell_idx;
            fifo_last_d[fifo_push_id_i] = push_cell_idx;

            cells_d[push_cell_idx].is_last = 1'b1;
            
        end else begin
            if (push_i) begin

                fifo_last_d[fifo_push_id_i] = push_cell_idx;
                cells_d[push_cell_idx].is_last = 1'b1;

                if (fifo_empty_q[fifo_push_id_i]) begin
                    fifo_head_d[fifo_push_id_i] = push_cell_idx;
                    fifo_empty_d[fifo_push_id_i] = 1'b0;
                end else begin
                    cells_d[fifo_last_q[fifo_push_id_i]].next = push_cell_idx;
                    cells_d[fifo_last_q[fifo_push_id_i]].is_last = 1'b0;    
                end
            end

            if (pop_i) begin
                fifo_head_d[fifo_pop_id_i] = cells_q[fifo_head_q[fifo_pop_id_i]].next;
                fifo_empty_d[fifo_pop_id_i] = cells_q[fifo_head_q[fifo_pop_id_i]].is_last;
            end
        end
    end

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
            cells_q <= '0;
            free_cells_q <= '0;
            fifo_head_q <= '0;
            fifo_last_q <= '0;
            fifo_empty_q <= '1;
            fifo_static_occup_q <= '0;
        end else begin
            cells_q <= cells_d;
            free_cells_q <= free_cells_d;
            fifo_head_q <= fifo_head_d;
            fifo_last_q <= fifo_last_d;
            fifo_empty_q <= fifo_empty_d;    
            fifo_static_occup_q <= fifo_static_occup_d;
        end
    end
endmodule
