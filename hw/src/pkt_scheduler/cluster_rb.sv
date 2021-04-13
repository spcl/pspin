// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/* 
    An allocator which manages memory as a ring-buffer. All allocations requests 
    are always served from the tail_ptr. It allocates only contiguous memory regions, so
    an allocation cannot wrap around: 
     - if head_ptr =< tail_ptr, the available space is max(mem_region_end - tail_ptr, head_ptr). 
     - if head_ptr > tail_ptr, the available space is head_ptr - tail_ptr.

    Free are not treated as FIFO pops, but they came with their own memory index, i.e., the index
    at which the memory region to free starts, and size. A memory index to free is not necesserly
    equal to the head_ptr but can be samewhere in between head_ptr and tail_ptr. The head_ptr is
    moved forward only when there is a consecutive free memory region in front of it. 
*/

module cluster_rb #(
    parameter int unsigned BuffMemLength = 1,
    parameter int unsigned MemSlotSize = 64, //[B]

    //derived parameters
    parameter type elem_size_t = logic [$clog2(BuffMemLength):0],
    parameter type elem_idx_t = logic [$clog2(BuffMemLength)-1:0],
    parameter int unsigned NumSlots = BuffMemLength / MemSlotSize
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

    /* we take the minimum allocatable unit as parameter, this is MemSlotSize. 
       Internally, we represent memory as a sequence of blocks of size MemSlotSize. 
    */
    typedef logic [$clog2(NumSlots)-1:0] slot_ptr_t;
    typedef logic [$clog2(NumSlots):0]   slot_size_t;
    
    logic [NumSlots-1:0] bitmap_d;
    logic [NumSlots-1:0] bitmap_q;

    slot_ptr_t head_ptr_d, head_ptr_q;
    slot_ptr_t tail_ptr_d, tail_ptr_q;
    
    slot_ptr_t push_idx, pop_idx;
    slot_size_t push_size, pop_size;

    logic [NumSlots*2-1:0]  bitmap_to_shift;
    logic [NumSlots-1:0]    bitmap_shifted;

    logic push_en, pop_en;

    slot_ptr_t head_ptr_incr_lzc;
    slot_size_t head_ptr_incr;
    slot_size_t head_ptr_incr_max;
    slot_size_t head_ptr_incr_real;
    logic no_head_ptr_incr;

    slot_size_t padding;
    logic data_fits;

    logic equal_full, equal_empty;

    slot_size_t free_slots, free_slots_to_end, free_slots_to_head;

    //the idea is to store the status of the memory blocks in a bitmap.
    for (genvar i=0; i<NumSlots; i++) begin: gen_bitmap_logic
        assign bitmap_d[i] = bitmap_q[i] ^ ((push_en && i >= push_idx && i < push_idx + push_size) || (pop_en && i >= pop_idx && i < pop_idx + pop_size));
    end

    //the bitmap is shifted right by head_ptr_q, so to let lzc count the number of consecutive free blocks and use 
    //that information to update head_ptr_q. 

    assign head_ptr_incr_max = (tail_ptr_q >= head_ptr_q) ? tail_ptr_q - head_ptr_q : tail_ptr_q + NumSlots - head_ptr_q;
    assign head_ptr_incr = head_ptr_incr_lzc + no_head_ptr_incr;
    assign head_ptr_incr_real = (head_ptr_incr_max > head_ptr_incr) ? head_ptr_incr : head_ptr_incr_max;

    assign bitmap_to_shift = { bitmap_q, bitmap_q } ; // input is the 512 bit bitmap
    assign bitmap_shifted =  bitmap_to_shift[head_ptr_q +: NumSlots];

    //get increment of head_ptr;
    lzc #(
        .WIDTH  (NumSlots)
    ) i_lzc_head_ptr_incr (
        .in_i    (bitmap_shifted),
        .cnt_o   (head_ptr_incr_lzc),
        .empty_o (no_head_ptr_incr)
    );

    
    assign push_en = data_fits && alloc_valid_i;
    assign pop_en = free_valid_i;

    assign pop_idx = free_index_i / MemSlotSize;
    assign push_idx = tail_ptr_q + padding;

    assign push_size = (alloc_size_i + MemSlotSize - 1) / MemSlotSize;
    assign pop_size  = (free_size_i + MemSlotSize - 1) / MemSlotSize;

    assign alloc_ready_o = push_en;
    assign alloc_index_o = push_idx * MemSlotSize;

    assign equal_full  = (head_ptr_q == tail_ptr_q && bitmap_q > 0);
    assign equal_empty  = (head_ptr_q == tail_ptr_q && bitmap_q == 0);

    //meaningful only if tail_ptr_q >= head_ptr_q
    assign free_slots_to_end = NumSlots - tail_ptr_q;
    assign free_slots_to_head = head_ptr_q;

    assign free_space_o = free_slots * MemSlotSize;

    //determine number of consecutive slots available
    always_comb begin
        free_slots = 0;
        if (!equal_full) begin
            if (head_ptr_q <= tail_ptr_q) begin   
                free_slots = (free_slots_to_end > free_slots_to_head) ? free_slots_to_end : free_slots_to_head;
            end
            else begin
                free_slots = head_ptr_q - tail_ptr_q;
            end
        end
    end

    always_comb begin
        head_ptr_d = head_ptr_q + head_ptr_incr_real;
        tail_ptr_d = (push_en) ? tail_ptr_q + padding + push_size : tail_ptr_q;

        //if everything is quiet and the buffer is empty, reset the pointers to zero
        //so to regain the full space.
        if (!push_en && !pop_en && equal_empty) begin
            head_ptr_d = '0;
            tail_ptr_d = '0;
        end
    end

    //check if data fits
    always_comb begin
        data_fits = 1'b0;
        padding = '0;

        if (!equal_full) begin
            if (head_ptr_q <= tail_ptr_q) begin   
                if (NumSlots - tail_ptr_q >= push_size) begin
                    // |<- start    | <- pop   | <-push   [data fits here]   | <- end
                    data_fits = 1'b1;
                end
                else if (push_size < head_ptr_q) begin //FIXME: this should be <= ?
                    // |<- start  [data fits here]  | <- pop   | <-push   | <- end
                    //push doesn't fit there, we start from 0    
                    data_fits = 1'b1;
                    padding = NumSlots - tail_ptr_q;
                end
            end
            else if (tail_ptr_q - head_ptr_q >= push_size) begin
                // |<- start  | <- push   [data fits here]  | <-pop   | <- end
                data_fits = 1'b1;
            end
        end
    end

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
            bitmap_q <= '0;
            head_ptr_q <= '0;
            tail_ptr_q <= '0;
        end else begin
            bitmap_q <= bitmap_d;
            head_ptr_q <= head_ptr_d;
            tail_ptr_q <= tail_ptr_d;
        end
    end

endmodule
