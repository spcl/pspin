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
#define LEARNING_RATE 1
#define INLINE inline

#define SCRATCHPAD(x) ((uint8_t*)(task->scratchpad[(x)]))
#define SELF_SCRATCHPAD SCRATCHPAD(args->cluster_id)
#define MASTER_SCRATCHPAD SCRATCHPAD(0)

#define WEIGHT_SIZE (sizeof(DTYPE) * (VECTOR_LEN + 1))
#define SELF_WEIGHT ((DTYPE*)(SELF_SCRATCHPAD))
#define MASTER_WEIGHT ((DTYPE*)(MASTER_SCRATCHPAD))
#define HPU_WEIGHT(x) ((DTYPE*)(SCRATCHPAD((x))))
#define RWLOCK ((spin_rw_lock_t *)(MASTER_SCRATCHPAD + WEIGHT_SIZE))

static INLINE DTYPE predict(const DTYPE input[VECTOR_LEN], const DTYPE weight[VECTOR_LEN + 1], spin_rw_lock_t *fit_lock) {
  DTYPE dot = 0;
  if (fit_lock)
    spin_rw_lock_r_lock(fit_lock);
  for (int i = 0; i < VECTOR_LEN; ++i) {
    dot += input[i] * weight[i];
  }
  dot += weight[VECTOR_LEN];
  if (fit_lock)
    spin_rw_lock_r_unlock(fit_lock);
  return ACTIVATION_FN(dot);
}

// non-atomical in-place modification of weight
DTYPE fit_batch(const DTYPE *input, const DTYPE *res, int len, DTYPE weight[VECTOR_LEN + 1], spin_rw_lock_t *fit_lock) {
  for (int i = 0; i < len; ++i) {
    DTYPE e = res[i] - predict(input + i * VECTOR_LEN, weight, fit_lock);
    spin_rw_lock_w_lock(fit_lock);
    for (int k = 0; k < VECTOR_LEN; ++k) {
      weight[k] += LEARNING_RATE * e * input[i * VECTOR_LEN + k];
    }
    weight[VECTOR_LEN] += LEARNING_RATE * e;
    spin_rw_lock_w_unlock(fit_lock);
  }
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

// memory layout:
// cluster 0: weight [fit, predict] | rwlock [fit]
// cluster 1-3: weight [predict]
__handler__ void slp_l1_hh(handler_args_t *args)
{
  task_t *task = args->task;

  uint8_t *pkt_pld_ptr;
  uint32_t pkt_pld_len;
  GET_IP_UDP_PLD(task->pkt_mem, pkt_pld_ptr, pkt_pld_len);
  slp_frame_hdr_t *hdr_ptr = (slp_frame_hdr_t *)pkt_pld_ptr;
  //printf("hh type %#x count %d\n", hdr_ptr->type, hdr_ptr->count);

  if (hdr_ptr->type == TY_FIT_DATA) {
    RWLOCK->num_readers = 32;
    spin_lock_init(&RWLOCK->glock);
    if (args->cluster_id) {
      printf("FATAL: hh fit cluster not 0 but %d\n", args->cluster_id);
      while (true) {}
    }
  }

  //printf("hh weight: %d %d %d\n", MASTER_WEIGHT[0], MASTER_WEIGHT[1], MASTER_WEIGHT[2]);
}

__handler__ void slp_l1_ph(handler_args_t *args)
{
    task_t* task = args->task;

    uint8_t *pkt_pld_ptr;
    uint32_t pkt_pld_len;
    GET_IP_UDP_PLD(task->pkt_mem, pkt_pld_ptr, pkt_pld_len);
    slp_frame_hdr_t *hdr_ptr = (slp_frame_hdr_t *)pkt_pld_ptr;
    //printf("ph type %#x count %d\n", hdr_ptr->type, hdr_ptr->count);

    DTYPE *input_ptr = (DTYPE *)(pkt_pld_ptr + sizeof(slp_frame_hdr_t));
    DTYPE *res_ptr = input_ptr + VECTOR_LEN * hdr_ptr->count; // only for TY_FIT_DATA

    switch (hdr_ptr->type) {
      case TY_FIT_DATA:
        fit_batch(input_ptr, res_ptr, hdr_ptr->count, MASTER_WEIGHT, RWLOCK);
        break;
      case TY_PREDICT:
        for (uint32_t i = 0; i < hdr_ptr->count; ++i) {
          DTYPE res = predict(input_ptr + i * VECTOR_LEN, SELF_WEIGHT, NULL);
          *(input_ptr + i) = res;
        }
        spin_cmd_t put; // not checking status for this
        uint32_t pld_size = sizeof(slp_frame_hdr_t) + sizeof(DTYPE) * hdr_ptr->count;
        send_return(task->pkt_mem, pld_size, &put);
        break;
      default:
        // something is wrong: unrecognized type
        printf("unrecognized type %#x\n", hdr_ptr->type);
        break;
    }
}

__handler__ void slp_l1_th(handler_args_t *args)
{
    task_t* task = args->task;

    uint8_t *pkt_pld_ptr;
    uint32_t pkt_pld_len;
    GET_IP_UDP_PLD(task->pkt_mem, pkt_pld_ptr, pkt_pld_len);
    slp_frame_hdr_t *hdr_ptr = (slp_frame_hdr_t *)pkt_pld_ptr;

    //printf("th type %#x count %d\n", hdr_ptr->type, hdr_ptr->count);

    if (hdr_ptr->type != TY_FIT_DATA) {
      return;
    }

    if (args->cluster_id) {
      printf("FATAL: th cluster not 0 but %d\n", args->cluster_id);
      while (true) {}
    }

    for (int i = 1; i < NB_CLUSTERS; ++i) {
      for (int k = 0; k < VECTOR_LEN + 1; ++k) {
        HPU_WEIGHT(i)[k] = MASTER_WEIGHT[k];
      }
    }

    //printf("th weight: %d %d %d\n", MASTER_WEIGHT[0], MASTER_WEIGHT[1], MASTER_WEIGHT[2]);
}

void init_handlers(handler_fn *hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {slp_l1_hh, slp_l1_ph, slp_l1_th};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];
}
