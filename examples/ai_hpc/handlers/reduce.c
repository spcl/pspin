// Copyright 2022 ETH Zurich
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

#include "reduce.h"

__handler__ void reduce_l1_ph(handler_args_t *args)
{

    task_t* task = args->task;

    uint8_t *pkt_pld_ptr;
    uint32_t pkt_pld_len;
    GET_IP_UDP_PLD(task->pkt_mem, pkt_pld_ptr, pkt_pld_len);

    uint32_t *nic_pld_addr = (uint32_t*) pkt_pld_ptr;

    //reduce_mem_t *mem = (reduce_mem_t *)args->her->match_info.handler_mem;
    volatile int32_t *local_mem = (int32_t *)(task->scratchpad[args->cluster_id]);

    //we assume the number of msg size divides the pkt payload size
    for (uint32_t i = 0; i < pkt_pld_len / 4; i++)
    {
        amo_add(&(local_mem[i]), nic_pld_addr[i]);
    }

    // We do need atomics here, as each handler writes to the same adress as others in the same cluster.
}

void init_handlers(handler_fn * hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {NULL, reduce_l1_ph, NULL};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];
}
