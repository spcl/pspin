
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

#ifndef HOST
#include <handler.h>
#include <packets.h>
#include <spin_dma.h>
#else
#include <handler_profiler.h>
#endif

#define NUM_INT_OP_FAST 20
#define NUM_INT_OP_SLOW 500


volatile __attribute__((section(".l2_handler_data"))) uint8_t handler_mem[] = {0xde, 0xad, 0xbe, 0xef};

__handler__ void empty_ph(handler_args_t *args) 
{

    uint32_t* pkt_ptr_int = args->task->pkt_mem;
    uint32_t handler_cost = *pkt_ptr_int;

    //printf("##### handler cost: %lu\n", handler_cost);

    if (handler_cost == 0)
    {
        uint32_t flow_id = args->task->flow_id;

        if (flow_id % 2 == 0) {
            volatile int xx = 0;
            int x = xx;
            for (int i=0; i<NUM_INT_OP_FAST; i++) {
                x = x*i;
            }
            xx = x;    
            
        } else {
            volatile int xx = 0;
            int x = xx;
            for (int i=0; i<NUM_INT_OP_SLOW; i++) {
                x = x*i;
            }
            xx = x;    
        }
    } 
    else 
    {
        rt_time_wait_cycles(handler_cost);
    }
}

void init_handlers(handler_fn * hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {NULL, empty_ph, NULL};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];

    *handler_mem_ptr = (void*) handler_mem;
}

