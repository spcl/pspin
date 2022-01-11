
// Copyright 2020 ETH Zurich
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <handler.h>
#include <packets.h>

#include "lazylist.h"

typedef struct rb_state
{
    lazylist_t list;
    uint32_t next_expected_byte;
} rb_state_t;

__handler__ void ooorb_hh(handler_args_t *args) 
{
    rb_state_t* state = (rb_state_t*) (args->task->scratchpad[0]);

    // This should be done on the host and then the initialized memory should be copied on the NIC
    lazylist_init(&(state->list), NUM_SEGMENTS);
    state->next_expected_byte = 0;
}

__handler__ void ooorb_ph(handler_args_t *args) 
{
    rb_state_t* state = (rb_state_t*) (args->task->scratchpad[0]);
    lazylist_t* list = &(state->list);
    lazylist_range_t range;
    uint32_t* pkt_info = args->task->pkt_mem;
    uint32_t op = pkt_info[0];
    range.left = pkt_info[1];
    range.right = pkt_info[2];

    if (op == 0)
    {
        //printf("inserting range: [%lu, %lu]\n", range.left, range.right);
        lazylist_insert(list, range);
    } 
    else if (op == 1) 
    {
        uint32_t popped = lazylist_pop_front(list, state->next_expected_byte, &range);
        if (popped) {
            //printf("popped range: [%lu, %lu]\n", range.left, range.right);
            state->next_expected_byte = range.right + 1;
        }
    }
}

__handler__ void ooorb_th(handler_args_t *args) 
{

    rb_state_t* state = (rb_state_t*) (args->task->scratchpad[0]);
    lazylist_t* list = &(state->list);
    lazylist_range_t range;

    uint32_t popped = lazylist_pop_front(list, state->next_expected_byte, &range);

    lazylist_node_t *head = GET_NODE_PTR(list, list->head_idx);

    while (1)
    {
        printf("node: [%lu, %lu]\n", head->range.left, head->range.right);
        head = GET_NODE_PTR(list, head->next_idx);
        if (head->range.right == INT32_MAX) break;
    }
}


void init_handlers(handler_fn * hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {ooorb_hh, ooorb_ph, ooorb_th};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];
}

