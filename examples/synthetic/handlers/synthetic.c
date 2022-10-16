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

#include "synthetic.h"

__handler__ void synthetic_ph(handler_args_t *args) 
{
    task_t *task = args->task;
    benchmark_params_t params = *(benchmark_params_t *)task->handler_mem;
    uint64_t host_addr = ((uint64_t)task->host_mem_high << 32) | (task->host_mem_low);
    ip_hdr_t *ip_hdr = (ip_hdr_t *)task->pkt_mem;    
    uint8_t *payload_addr = (uint8_t *)ip_hdr;
    uint32_t payload_len = ip_hdr->length;
    udp_hdr_t *udp_hdr = (udp_hdr_t *)(payload_addr + ip_hdr->ihl * 4);
    uint32_t res = 0;
    uint32_t src_id;
    uint16_t src_port;
    spin_cmd_t comp;

    for (int i = 0; i < params.loop_spin_count; i++)
	res += i;

    if (params.dma_to_count > 0 && params.dma_to_size > 0) {
	for (int i = 0; i < params.dma_to_count; i++) {
	    spin_dma_to_host(host_addr, (uint32_t)payload_addr, params.dma_to_size, 1, &comp);
	    spin_cmd_wait(comp);
	}
    }

    src_id = ip_hdr->source_id;
    ip_hdr->source_id = ip_hdr->dest_id;
    ip_hdr->dest_id = src_id;

    src_port = udp_hdr->src_port;
    udp_hdr->src_port = udp_hdr->dst_port;
    udp_hdr->dst_port = src_port;

    if (params.dma_from_count > 0 && params.dma_from_size > 0) {
	for (int i = 0; i < params.dma_from_count; i++) {
	    spin_dma_from_host(host_addr, (uint32_t)payload_addr, params.dma_from_size, 1, &comp);
	    spin_cmd_wait(comp);
	    spin_send_packet(payload_addr, payload_len, &comp);
	    spin_cmd_wait(comp);
	}
    }
}

void init_handlers(handler_fn * hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {NULL, synthetic_ph, NULL};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];
}
