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

#include "slp_l1.h"

#define NUM_CLUSTERS 4
#define STRIDE 1
#define OFFSET 0
#define NUM_INT_OP 0

#define ACTIVATION_FN(x) ((x) >= 0 ? 1 : 0)
#define LEARNING_RATE 1.0f
#define INLINE inline

INLINE DTYPE predict(const DTYPE input[VECTOR_LEN], const DTYPE weight[VECTOR_LEN + 1]) {
  DTYPE dot = 0.0f;
  for (int i = 0; i < VECTOR_LEN; ++i) {
    dot += input[i] * weight[i];
  }
  dot += weight[VECTOR_LEN];
  return dot;
}

// non-atomical in-place modification of weight
DTYPE fit_batch(const DTYPE *input, const DTYPE *res, int len, DTYPE weight[VECTOR_LEN + 1]) {
  for (int i = 0; i < len; ++i) {
    DTYPE e = res[i] - predict(input + i * VECTOR_LEN, weight);
    for (int k = 0; k < VECTOR_LEN; ++k) {
      weight[k] += LEARNING_RATE * e * input[i * VECTOR_LEN + k];
    }
    weight[VECTOR_LEN] += LEARNING_RATE * e;
  }
}
void dump_slp_hdr(uint32_t hpu_id, uint32_t cluster_id, slp_frame_hdr_t *hdr_ptr) {
  printf("Cluster %d HPU %d type %#x count %d serial_no %d\n", cluster_id, hpu_id, hdr_ptr->type, hdr_ptr->count, hdr_ptr->serial_no);
}

// pkt_mem includes IP and UDP headers
// payload_size does not include IP and UDP headers
void send_return(uint8_t *pkt_mem, uint8_t payload_size, spin_cmd_t *put) {
  ip_hdr_t *ip_hdr = (ip_hdr_t*)pkt_mem;
  udp_hdr_t *udp_hdr = (udp_hdr_t*)((uint8_t*)pkt_mem + ip_hdr->ihl * 4);

  ip_hdr->length = ip_hdr->ihl * 4 + sizeof(udp_hdr_t) + payload_size;
  udp_hdr->length = sizeof(udp_hdr_t) + payload_size;

  uint32_t src_id = ip_hdr->source_id;
  ip_hdr->source_id = ip_hdr->dest_id;
  ip_hdr->dest_id = src_id;

  uint16_t src_port = udp_hdr->src_port;
  udp_hdr->src_port = udp_hdr->dst_port;
  udp_hdr->dst_port = src_port;

  // we should fix IP and UDP checksums here

  spin_send_packet(pkt_mem, ip_hdr->length, put);
}

__handler__ void slp_l1_ph(handler_args_t *args)
{
    task_t* task = args->task;

    uint8_t *pkt_pld_ptr;
    uint32_t pkt_pld_len;
    GET_IP_UDP_PLD(task->pkt_mem, pkt_pld_ptr, pkt_pld_len);

    slp_frame_hdr_t *hdr_ptr = (slp_frame_hdr_t *)pkt_pld_ptr;
    int32_t *local_mem = (int32_t*) (task->scratchpad[args->cluster_id]);
    printf("pkt_mem: %#x, pkt_mem_size: %ld, l2_pkt_mem: %#x\n", task->pkt_mem, task->pkt_mem_size, task->l2_pkt_mem);
    dump_slp_hdr(args->hpu_id, args->cluster_id, hdr_ptr);

    uint32_t *hpu_serial_no = (uint32_t*)((uint8_t*)local_mem + ((VECTOR_LEN + 1) * sizeof(DTYPE) + sizeof(uint32_t)) * args->hpu_id);
    DTYPE *hpu_weight = (DTYPE*)(hpu_serial_no + 1);

    DTYPE *input_ptr = (DTYPE *)(pkt_pld_ptr + sizeof(slp_frame_hdr_t));
    DTYPE *res_ptr = input_ptr + VECTOR_LEN * hdr_ptr->count; // only for TY_FIT_DATA
    switch (hdr_ptr->type) {
      case TY_FIT_DATA:
        fit_batch(input_ptr, res_ptr, hdr_ptr->count, hpu_weight);
        break;
      case TY_PREDICT:
        for (uint32_t i = 0; i < hdr_ptr->count; ++i) {
          DTYPE res = predict(input_ptr + i * VECTOR_LEN, hpu_weight);
          *(input_ptr + i) = res;
        }
        spin_cmd_t put; // not checking status for this
        uint32_t pld_size = sizeof(slp_frame_hdr_t) + sizeof(DTYPE) * hdr_ptr->count;
        send_return(task->pkt_mem, pld_size, &put);
        break;
      case TY_END_FITTING:
        // TODO ignore synchronization for now
        break;
    }
}

__handler__ void slp_l1_th(handler_args_t *args)
{
    task_t* task = args->task;
    uint64_t host_address = task->host_mem_high;
    host_address = (host_address << 32) | (task->host_mem_low);

    //signal that we completed so to let the host read the weight back
    spin_host_write(host_address, (uint64_t) 1, false);
}

void init_handlers(handler_fn *hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {NULL, slp_l1_ph, slp_l1_th};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];
}
