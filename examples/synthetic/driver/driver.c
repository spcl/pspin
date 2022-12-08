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

#include <string.h>
#include <stdio.h>
#include <assert.h>

#include "gdriver.h"
#include "packets.h"
#include "../handlers/synthetic.h"



int match_ectx_cb(char *arg1, char *arg2)
{
    const char *src_addr = arg1; // arg1 is source address of packet in trace
    const char *ectx_match_addr = arg2;

    if (!strcmp(src_addr, ectx_match_addr)) {
        printf("DEBUG: %s %s\n", src_addr, ectx_match_addr);
        return 1;
    }

    return 0;
}

uint32_t fill_packet(uint32_t msg_idx, void *data,
    uint8_t *pkt_buf, uint32_t pkt_size, uint32_t* l1_pkt_size)
{
    pkt_hdr_t *hdr;
    uint32_t *hpu_cost;

    assert(sizeof(pkt_hdr_t) + sizeof(uint32_t) <= pkt_size);

    // generate IP+UDP headers
    hdr = (pkt_hdr_t *)pkt_buf;
    hdr->ip_hdr.ihl = 5;
    hdr->ip_hdr.length = pkt_size;
    *l1_pkt_size = pkt_size;

    hpu_cost = (uint32_t *)(pkt_buf + sizeof(pkt_hdr_t));
    *hpu_cost = *(uint32_t *)data;

    return pkt_size;
}

int main(int argc, char **argv)
{
    const char *handlers_file = "build/synthetic";
    const char *hh = NULL;
    const char *ph = "synthetic_ph";
    const char *th = NULL;
    const char *base_addr = "192.168.0.";
    char matching_addr[GDRIVER_MATCHING_CTX_MAXSIZE];
    benchmark_params_t params;
    int ectx_num, ret;

    params.loop_spin_count = 1000000;
    params.dma_to_size = 64;
    params.dma_to_count = 0;
    params.dma_from_size = 64;
    params.dma_from_count = 0;

    if (gdriver_init(argc, argv, match_ectx_cb, &ectx_num) != GDRIVER_OK)
        return EXIT_FAILURE;

    for (int ectx_id = 0; ectx_id < ectx_num; ectx_id++) {
        sprintf(matching_addr, "%s%u", base_addr, ectx_id + 1);
        ret = gdriver_add_ectx(handlers_file, hh, ph, th,
                               fill_packet,
                               (void *)&params,
                               sizeof(params),
                               matching_addr,
                               strlen(matching_addr) + 1);
        if (ret != GDRIVER_OK) {
            return EXIT_FAILURE;
        }
    }

    if (gdriver_run() != GDRIVER_OK)
        return EXIT_FAILURE;

    return (gdriver_fini() == GDRIVER_OK) ? EXIT_SUCCESS : EXIT_FAILURE;
}
