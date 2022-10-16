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

#include <stdint.h>
#include <stdio.h>
#include <stdbool.h>
#include "gdriver.h"
#include "packets.h"

#include "../handlers/slp_l1.h"

#define F(data) ((data)[0] - 2 * (data)[1] > 1)

const DTYPE fit_data[8][2] = {
  8, 1,
  6, 1,
  8, 1,
  1, 2,
  2, 4,
  6, 1,
  4, 6,
  5, 3
};
const DTYPE fit_result[8] = {
  1, 1, 1, 0, 0, 1, 0, 0
};

// final weight should be 2, -9, -1

#define HISTOGRAM_WORDS 1024
#define SEED 236695

void hexdump(const void* data, size_t size) {
  char ascii[17];
  size_t i, j;
  ascii[16] = '\0';
  for (i = 0; i < size; ++i) {
    printf("%02X ", ((unsigned char*)data)[i]);
    if (((unsigned char*)data)[i] >= ' ' && ((unsigned char*)data)[i] <= '~') {
      ascii[i % 16] = ((unsigned char*)data)[i];
    } else {
      ascii[i % 16] = '.';
    }
    if ((i+1) % 8 == 0 || i+1 == size) {
      printf(" ");
      if ((i+1) % 16 == 0) {
        printf("|  %s \n", ascii);
      } else if (i+1 == size) {
        ascii[(i+1) % 16] = '\0';
        if ((i+1) % 16 <= 8) {
          printf(" ");
        }
        for (j = (i+1) % 16; j < 16; ++j) {
          printf("   ");
        }
        printf("|  %s \n", ascii);
      }
    }
  }
}

bool diag_printed = false;
bool predict_only = false;

// 3 messages: fit, end-of-fit, predict
uint32_t fill_packet(uint32_t msg_idx, uint32_t pkt_idx, uint8_t *pkt_buff, uint32_t max_pkt_size, uint32_t* l1_pkt_size)
{
    int payload_max_size = max_pkt_size - sizeof(pkt_hdr_t) - sizeof(slp_frame_hdr_t);
    int batch = -1;
    int fit_batch = payload_max_size / ((VECTOR_LEN + 1) * sizeof(DTYPE));
    int predict_batch = payload_max_size / (VECTOR_LEN * sizeof(DTYPE));
    uint8_t ty;
    uint32_t payload_len = sizeof(slp_frame_hdr_t);

    if (!predict_only && msg_idx == 0) {
      ty = TY_FIT_DATA;
      batch = fit_batch;
      payload_len += (VECTOR_LEN + 1) * batch * sizeof(DTYPE);
    } else {
      ty = TY_PREDICT;
      batch = predict_batch;
      payload_len += VECTOR_LEN * batch * sizeof(DTYPE);
    }

    //printf("filling packet msg_idx=%d pkt_idx=%d ty=%#x\n", msg_idx, pkt_idx, ty);
    if (!diag_printed) {
      printf("Packet payload max size %d\n", payload_max_size);
      printf("Fit batch size: %d; predict batch size: %d\n", fit_batch, predict_batch);
      diag_printed = true;
    }

    pkt_hdr_t *hdr = (pkt_hdr_t*) pkt_buff;
    hdr->ip_hdr.ihl = 5;
    hdr->udp_hdr.length = payload_len + sizeof(udp_hdr_t);
    hdr->ip_hdr.length = hdr->udp_hdr.length + hdr->ip_hdr.ihl * 4;

    // for magic
    hdr->udp_hdr.src_port = 0xdead;
    hdr->udp_hdr.dst_port = 0xbeef;

    if (hdr->ip_hdr.length > max_pkt_size) {
      printf("Requested packet size %d but largest possible is %d, aborting\n", hdr->ip_hdr.length, max_pkt_size);
      abort();
    }

    slp_frame_hdr_t *pld_hdr = (slp_frame_hdr_t*)((uint8_t*)pkt_buff + sizeof(pkt_hdr_t));
    pld_hdr->type = ty;
    pld_hdr->count = batch;

    DTYPE *pld_body = (DTYPE *)((uint8_t*)pld_hdr + sizeof(slp_frame_hdr_t));

    for (int i = 0; i < batch; ++i) {
      int sample_idx = i % 8;
      for (int k = 0; k < VECTOR_LEN; ++k) {
        pld_body[i * VECTOR_LEN + k] = ty == TY_FIT_DATA ? fit_data[sample_idx][k] : rand();
      }
      if (ty == TY_FIT_DATA) {
        DTYPE res = F(pld_body + i * VECTOR_LEN);
        if (res != fit_result[sample_idx]) {
          printf("ERR: result mismatch for sample %d\n", i);
          abort();
        }
        pld_body[batch * VECTOR_LEN + i] = res;
      }
    }

    //hexdump(pkt_buff, hdr->ip_hdr.length);

    //return max_pkt_size;
    return hdr->ip_hdr.length;
}

int main(int argc, char**argv)
{
    const char *handlers_file = "build/slp_l1";
    const char *hh = "slp_l1_hh";
    const char *ph = "slp_l1_ph";
    const char *th = "slp_l1_th";
    int ectx_num;

    srand(SEED);

    predict_only = getenv("PREDICT_ONLY") != NULL;
    if (predict_only) {
        printf("Note: running prediction only");
    }

    gdriver_init(argc, argv, NULL, &ectx_num);
    gdriver_add_ectx(handlers_file, hh, ph, th, fill_packet, NULL, 0, NULL, 0);

    gdriver_run();

    gdriver_fini();

    return 0;
}
