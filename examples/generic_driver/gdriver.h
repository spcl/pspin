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

#pragma once

#define GDRIVER_OK 0 
#define GDRIVER_ERR 1

#include <stdint.h>
#include <stdlib.h>

typedef uint32_t (*fill_packet_fun_t)(uint32_t, uint32_t, uint8_t*, uint32_t, uint32_t*);


int gdriver_init(int argc, char** argv, const char* hfile, const char* hh, const char* ph, const char* th);
int gdriver_fini();
int gdriver_set_packet_fill_callback(fill_packet_fun_t pkt_fill_fun);
int gdriver_set_l2_img(void *img, size_t size);
int gdriver_run();
void gdriver_enqueue_pkt(uint32_t msg_idx, void* pkt_buff, uint32_t pkt_size, uint32_t l1_pkt_size, uint8_t is_last, uint32_t delay);
