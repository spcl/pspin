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
#else
#include <handler_profiler.h>
#endif

#include <packets.h>
#include <spin_conf.h>

#define NUM_CLUSTERS 4
#define STRIDE 1
#define OFFSET 0
#define NUM_INT_OP 0

#define HISTOGRAM_SIZE 1024

__handler__ void histogram_l1_ph(handler_args_t *args)
{
    task_t* task = args->task;
    
    uint8_t *pkt_pld_ptr;
    uint32_t pkt_pld_len;
    GET_IP_UDP_PLD(task->pkt_mem, pkt_pld_ptr, pkt_pld_len);

    int32_t *nic_pld_addr = (int32_t*) pkt_pld_ptr;

    int32_t *local_mem = (int32_t*) (task->scratchpad[args->cluster_id]);
    
    volatile int32_t* word_ptr = &(local_mem[nic_pld_addr[0]]);

    //we assume the number of msg size divides the pkt payload size
    for (uint32_t i = 1; i < pkt_pld_len / 4; i++)
    {
        amo_add(word_ptr, 1); 
        word_ptr = &(local_mem[nic_pld_addr[i]]);
    }
}

__handler__ void histogram_l1_th(handler_args_t *args)
{
    task_t* task = args->task;
    uint64_t host_address = task->host_mem_high;
    host_address = (host_address << 32) | (task->host_mem_low);

    //signal that we completed so to let the host read the result back
    spin_host_write(host_address, (uint64_t) 1, false);
}

void init_handlers(handler_fn *hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {NULL, histogram_l1_ph, histogram_l1_th};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];
}
