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

//#define SLP_LOG(format, ...) printf("[slp] " format "\n", ##__VA_ARGS__);
#define SLP_LOG(format, ...)

static INLINE DTYPE predict(const DTYPE input[VECTOR_LEN], const DTYPE weight[VECTOR_LEN + 1], spin_rw_lock_t *fit_lock) {
  //SLP_LOG("predict input=%#x weight=%#x", input, weight);
  DTYPE dot = 0;
  if (fit_lock)
    spin_rw_lock_r_lock(fit_lock);
  for (int i = 0; i < VECTOR_LEN; ++i) {
    dot += input[i] * weight[i];
  }
  dot += weight[VECTOR_LEN];
  if (fit_lock)
    spin_rw_lock_r_unlock(fit_lock);
  return dot;
}

// non-atomical in-place modification of weight
DTYPE fit_batch(const DTYPE *input, const DTYPE *res, int len, DTYPE weight[VECTOR_LEN + 1], spin_rw_lock_t *fit_lock) {
  SLP_LOG("fit_batch input=%#x res=%#x len=%d weight=%#x", input, res, len, weight);
  for (int i = 0; i < len; ++i) {
    DTYPE e = res[i] - predict(input + i * VECTOR_LEN, weight, fit_lock);
    spin_rw_lock_w_lock(fit_lock);
    for (int k = 0; k < VECTOR_LEN; ++k) {
      weight[k] += LEARNING_RATE * e * input[i * VECTOR_LEN + k];
    }
    weight[VECTOR_LEN] += LEARNING_RATE * e;
    spin_rw_lock_w_unlock(fit_lock);
    //printf("left critical region\n");
  }
}

// pkt_mem includes IP and UDP headers
// payload_size does not include IP and UDP headers
void send_return(uint8_t *pkt_mem, uint8_t payload_size, spin_cmd_t *put) {
  SLP_LOG("send_return pkt_mem=%#x payload_size=%d", pkt_mem, payload_size);
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
// cluster 0: weight [fit, predict] | rwlock [fit] | predict_flag [predict]
// cluster 1-3: weight [predict]
__handler__ void slp_l1_hh(handler_args_t *args)
{
  task_t *task = args->task;

  if (args->cluster_id) {
    //printf("FATAL: hh cluster not 0 but %d\n", args->cluster_id);
    while (true) {}
  }

  //printf("START: initialize rw lock\n");
  uint8_t *local_mem = (uint8_t*)(task->scratchpad[args->cluster_id]);

  spin_rw_lock_t *fit_lock = (spin_rw_lock_t*)(local_mem + sizeof(DTYPE) * (VECTOR_LEN + 1));

  fit_lock->num_readers = 32;
  spin_lock_init(&fit_lock->glock);

  volatile uint32_t *predict_flag = (uint32_t *)(local_mem + sizeof(DTYPE) * (VECTOR_LEN + 1) + sizeof(spin_rw_lock_t));
  *predict_flag = 0;
}

__handler__ void slp_l1_ph(handler_args_t *args)
{
    task_t* task = args->task;

    uint8_t *pkt_pld_ptr;
    uint32_t pkt_pld_len;
    GET_IP_UDP_PLD(task->pkt_mem, pkt_pld_ptr, pkt_pld_len);

    slp_frame_hdr_t *hdr_ptr = (slp_frame_hdr_t *)pkt_pld_ptr;
    uint8_t *local_mem = (uint8_t*) (task->scratchpad[args->cluster_id]);
    uint8_t *master_mem = (uint8_t*)(task->scratchpad[0]);
    //printf("type %#x count %d serial_no %d\n", hdr_ptr->type, hdr_ptr->count, hdr_ptr->serial_no);

    volatile uint32_t *local_serial_no = (uint32_t*)(local_mem + (VECTOR_LEN + 1) * sizeof(DTYPE));
    DTYPE *fit_weight = (DTYPE *)(master_mem);
    spin_rw_lock_t *fit_lock = (spin_rw_lock_t *)(master_mem + sizeof(DTYPE) * (VECTOR_LEN + 1));

    volatile uint32_t *predict_flag = (uint32_t*)(master_mem + sizeof(DTYPE) * (VECTOR_LEN + 1) + sizeof(spin_rw_lock_t));
    DTYPE *predict_weight = (DTYPE *)(local_mem);

    DTYPE *input_ptr = (DTYPE *)(pkt_pld_ptr + sizeof(slp_frame_hdr_t));
    DTYPE *res_ptr = input_ptr + VECTOR_LEN * hdr_ptr->count; // only for TY_FIT_DATA

    switch (hdr_ptr->type) {
      case TY_FIT_DATA:
        fit_batch(input_ptr, res_ptr, hdr_ptr->count, fit_weight, fit_lock);
        amo_maxu(local_serial_no, hdr_ptr->serial_no);
        break;
      case TY_PREDICT:
        while (!*predict_flag) {}
        for (uint32_t i = 0; i < hdr_ptr->count; ++i) {
          DTYPE res = predict(input_ptr + i * VECTOR_LEN, predict_weight, NULL);
          *(input_ptr + i) = res;
        }
        spin_cmd_t put; // not checking status for this
        uint32_t pld_size = sizeof(slp_frame_hdr_t) + sizeof(DTYPE) * hdr_ptr->count;
        send_return(task->pkt_mem, pld_size, &put);
        break;
      case TY_END_FITTING: {
        // get serial no for last fit
        uint32_t last_seq = *(uint32_t *)(input_ptr);
        while (true) {
          uint32_t max_seq = 0;
          for (int i = 0; i < NB_CLUSTERS; ++i) {
            uint32_t slave_seq = *(volatile uint32_t*)((uint8_t*)task->scratchpad[i] + sizeof(DTYPE) * (VECTOR_LEN + 1));
            max_seq = max_seq > slave_seq ? max_seq : slave_seq;
          }
          if (max_seq == last_seq) break;
        }
        spin_rw_lock_r_lock(fit_lock);
        for (int i = 1; i < NB_CLUSTERS; ++i) {
          uint8_t *slave_mem = (uint8_t*)(task->scratchpad[i]);
          DTYPE *slave_weight = (DTYPE*)(slave_mem);
          for (int k = 0; k < VECTOR_LEN + 1; ++k) {
            slave_weight[k] = fit_weight[k];
          }
        }
        // deliberately not unlocking: no fitting packet should come in after this point
        //spin_rw_lock_r_unlock(fit_lock);
        amo_store(predict_flag, 1);
        break;
                           }
      default:
        // something is wrong: unrecognized type
        SLP_LOG("unrecognized type %#x", hdr_ptr->type);
        break;
    }
}

__handler__ void slp_l1_th(handler_args_t *args)
{
    task_t* task = args->task;
    uint64_t host_address = task->host_mem_high;
    host_address = (host_address << 32) | (task->host_mem_low);

    uint32_t max_seq = 0;
    for (int i = 0; i < NB_CLUSTERS; ++i) {
      uint32_t slave_seq = *(volatile uint32_t*)((uint8_t*)task->scratchpad[i] + sizeof(DTYPE) * (VECTOR_LEN + 1));
      max_seq = max_seq > slave_seq ? max_seq : slave_seq;
    }
    uint8_t *master_mem = (uint8_t*) (task->scratchpad[0]);
    DTYPE *hpu_weight = (DTYPE*)(master_mem);
    printf("training end serial no: %d\n", max_seq);
    printf("weight: %d %d %d\n", hpu_weight[0], hpu_weight[1], hpu_weight[2]);

    //signal that we completed so to let the host read the weight back
    spin_host_write(host_address, (uint64_t) 1, false);
}

void init_handlers(handler_fn *hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {slp_l1_hh, slp_l1_ph, slp_l1_th};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];
}
