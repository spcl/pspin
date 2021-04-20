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

    gdriver_init(argc, argv, handlers_file, hh, ph, th);
    gdriver_set_packet_fill_callback(fill_packet);
   
    gdriver_run();

    gdriver_fini();
    return 0;
}
