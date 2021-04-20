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

#if !defined(TO_L2) && !defined(TO_L1)
#define TO_L1
#endif

__handler__ void copy_from_host_ph(handler_args_t *args)
{
    task_t* task = args->task;
    ip_hdr_t *ip_hdr = (ip_hdr_t*) (task->pkt_mem);
#ifndef TO_L1
    uint8_t *nic_pld_addr = ((uint8_t*) (task->l2_pkt_mem)); 
#else
    uint8_t *nic_pld_addr = ((uint8_t*) (task->pkt_mem)); 
#endif
    uint16_t pkt_pld_len = ip_hdr->length;
    udp_hdr_t *udp_hdr = (udp_hdr_t*) (((uint8_t*) (task->pkt_mem)) + ip_hdr->ihl * 4);

    uint32_t src_id = ip_hdr->source_id;
    ip_hdr->source_id = ip_hdr->dest_id;
    ip_hdr->dest_id = src_id;

    uint16_t src_port = udp_hdr->src_port;
    udp_hdr->src_port = udp_hdr->dst_port;
    udp_hdr->dst_port = src_port;

    spin_cmd_t dma;

    uint64_t host_address = task->host_mem_high;
    host_address = (host_address << 32) | (task->host_mem_low);
    spin_dma_from_host(host_address, (uint32_t) nic_pld_addr, pkt_pld_len, 1, &dma);

    spin_cmd_wait(dma);

    spin_cmd_t send;
    spin_send_packet(nic_pld_addr, pkt_pld_len, &send);
}

void init_handlers(handler_fn * hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {NULL, copy_from_host_ph, NULL};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];

}
