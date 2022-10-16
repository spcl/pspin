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
#include <assert.h>

#include "gdriver.h"

#include "../handlers/filtering.h"

#define SEED 6598736

uint16_t hashmult(const uint16_t key)
{
    uint16_t hash = 0;
    uint8_t *key_byte = (uint8_t *)&key;
    for (uint16_t i = 0; i < sizeof(uint16_t); i++)
    {
        //printf("i %u k %u",i,key_byte[i] );
        hash = hash * 31 + (key_byte[i]);
    }
    return hash;
}

void fill_htable(uint32_t *vec, uint32_t length)
{
    for (uint32_t i = 0; i < length; i++)
    {
        vec[hashmult((uint16_t)i)] = i;
    }
}

uint32_t fill_packet(uint32_t msg_idx, uint32_t pkt_idx, uint8_t *pkt_buff, uint32_t max_pkt_size, uint32_t *l1_pkt_size)
{
    assert(max_pkt_size >= KEY_SIZE);

    for (int i = 0; i < KEY_SIZE / sizeof(uint32_t); i++)
    {
        ((uint32_t *)pkt_buff)[i] = rand();
    }

    return max_pkt_size;
}

int main(int argc, char **argv)
{
    const char *handlers_file = "build/filtering";
    const char *hh = NULL;
    const char *ph = "filtering_ph";
    const char *th = NULL;
    int ectx_num;

    srand(SEED);

    uint32_t *vec = (uint32_t *)malloc(sizeof(uint32_t) * (TOT_WORDS));
    fill_htable(vec, TOT_WORDS);

    gdriver_init(argc, argv, NULL, &ectx_num);
    gdriver_add_ectx(handlers_file, hh, ph, th, fill_packet,
        (void *)vec, sizeof(uint32_t) * (TOT_WORDS), NULL, 0);

    gdriver_run();

    gdriver_fini();

    free(vec);

    return 0;
}
