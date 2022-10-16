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
#include "gdriver.h"

uint32_t fill_packet(uint32_t msg_idx, uint32_t pkt_idx, uint8_t *pkt_buff, uint32_t max_pkt_size, uint32_t* l1_pkt_size)
{
    // nothing to do here

    return max_pkt_size;
}

int main(int argc, char**argv)
{
    const char *handlers_file="build/empty";
    const char *hh="empty_hh";
    const char *ph="empty_ph";
    const char *th="empty_th";
    int ectx_num;

    gdriver_init(argc, argv, NULL, &ectx_num);
    gdriver_add_ectx(handlers_file, hh, ph, th, fill_packet, NULL, 0, NULL, 0);

    gdriver_run();

    return (gdriver_fini()) ? EXIT_SUCCESS : EXIT_FAILURE;
}
