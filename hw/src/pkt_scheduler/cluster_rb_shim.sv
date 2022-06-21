// Copyright (c) 2022 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

import pspin_cfg_pkg::*;

module cluster_rb_shim #(

    parameter int unsigned BuffMemLength = 1,
    parameter int unsigned NumRB = 1,
    parameter int unsigned MemSlotSize = 64, //[B]

    //derived parameters
    parameter int unsigned BuffMemLenghtPerRB = BuffMemLength / NumRB,
    parameter type elem_size_t = logic [$clog2(BuffMemLength):0],
    parameter type elem_idx_t = logic [$clog2(BuffMemLength)-1:0],
    parameter type rb_elem_size_t = logic [$clog2(BuffMemLenghtPerRB):0],
    parameter type rb_elem_idx_t = logic [$clog2(BuffMemLenghtPerRB)-1:0]
    //parameter int unsigned NumSlotsPerRB = BuffMemLength / MemSlotSize
) (

    input  logic        clk_i,
    input  logic        rst_ni,

    input  logic        alloc_valid_i,
    output logic        alloc_ready_o,
    input  elem_size_t  alloc_size_i,   //[B] 
    output elem_idx_t   alloc_index_o,  //[B]

    input  logic        free_valid_i,
    input  elem_idx_t   free_index_i,   //[B]
    input  elem_size_t  free_size_i,    //[B]

    output elem_size_t  free_space_o    //[B]
);

    logic          [NumRB-1:0]          rb_with_space;
    rb_elem_size_t [NumRB-1:0]          rb_free_space;
    logic          [NumRB-1:0]          rb_ready;
    rb_elem_idx_t  [NumRB-1:0]          rb_alloc_index;
    rb_elem_size_t [NumRB-1:0]          rb_free_space_tmp_max;
    
    logic          [$clog2(NumRB)-1:0]  sel_rb_idx;

    for (genvar i = 0; i < NumRB; i++) begin : gen_rb

        rb_elem_idx_t free_idx_rel;
        logic freeing_ith_rb, free_valid;
        
        assign free_idx_rel = free_index_i % BuffMemLenghtPerRB;
        assign freeing_ith_rb = ((free_index_i / BuffMemLenghtPerRB) == i);
        assign free_valid = free_valid_i && freeing_ith_rb;

        cluster_rb #(
            .BuffMemLength  (BuffMemLenghtPerRB),
            .MemSlotSize    (MemSlotSize)
        ) i_her_alloc (
            .clk_i          (clk_i),
            .rst_ni         (rst_ni),

            .alloc_valid_i  (i == sel_rb_idx && alloc_valid_i),
            .alloc_ready_o  (rb_ready[i]),
            .alloc_size_i   (alloc_size_i),
            .alloc_index_o  (rb_alloc_index[i]),

            .free_valid_i   (free_valid),
            .free_index_i   (free_idx_rel),
            .free_size_i    (free_size_i),

            .free_space_o   (rb_free_space[i])
        );

        assign rb_with_space[i] = rb_free_space[i] >= alloc_size_i;

    end

    // select first RB that has enough space
    lzc #(
        .WIDTH  (NumRB)
    ) i_lzc_rb_selector (
        .in_i    (rb_with_space),
        .cnt_o   (sel_rb_idx),
        .empty_o ()
    );

    // free space is the max among all RBs free spaces
    assign rb_free_space_tmp_max[0] = rb_free_space[0];
    for (genvar i=1; i<NumRB; i++) begin : gen_slow_max
        assign rb_free_space_tmp_max[i] = (rb_free_space_tmp_max[i-1] >= rb_free_space[i]) ? rb_free_space_tmp_max[i-1] : rb_free_space[i];
    end 
    assign free_space_o = rb_free_space_tmp_max[NumRB-1];

    assign alloc_ready_o = rb_ready[sel_rb_idx];
    assign alloc_index_o = sel_rb_idx * BuffMemLenghtPerRB + rb_alloc_index[sel_rb_idx];

endmodule