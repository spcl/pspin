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

#define HWSCHED_HANDLER_FUN_ADDR     0x1B205000
#define HWSCHED_HANDLER_FUN_SIZE     0x1B205004
#define HWSCHED_HANDLER_MEM_ADDR     0x1B205008
#define HWSCHED_HANDLER_MEM_SIZE     0x1B20500c
#define HWSCHED_PKT_ADDR             0x1B205010
#define HWSCHED_PKT_SIZE             0x1B205014
#define HWSCHED_SCRATCHPAD_0_ADDR    0x1B205018
#define HWSCHED_SCRATCHPAD_1_ADDR    0x1B20501c
#define HWSCHED_SCRATCHPAD_2_ADDR    0x1B205020
#define HWSCHED_SCRATCHPAD_3_ADDR    0x1B205024
#define HWSCHED_SCRATCHPAD_0_SIZE    0x1B205028
#define HWSCHED_SCRATCHPAD_1_SIZE    0x1B20502c
#define HWSCHED_SCRATCHPAD_2_SIZE    0x1B205030
#define HWSCHED_SCRATCHPAD_3_SIZE    0x1B205034
#define HWSCHED_HOST_MEM_ADDR_HIGH   0x1B205038
#define HWSCHED_HOST_MEM_ADDR_LOW    0x1B20503c
#define HWSCHED_HOST_MEM_SIZE        0x1B205040
#define HWSCHED_HOST_L2_PKT_ADDR     0x1B205044
#define HWSCHED_HOME_CLUSTER_ID      0x1B205048
#define HWSCHED_FLOW_ID              0x1B20504c
#define HWSCHED_DOORBELL             0x1B205050
#define HWSCHED_ERROR                0x1B205054

#define CMD_ISSUE   0x1B205080
#define CMD_WAIT    0x1B205084
#define CMD_TEST    0x1B205088
#define CMD_INFO    0x1B20508C
#define CMD_WORD0   0x1B205090
#define CMD_WORD1   0x1B205094
#define CMD_WORD2   0x1B205098
#define CMD_WORD3   0x1B20509C
#define CMD_WORD4   0x1B2050A0
#define CMD_WORD5   0x1B2050A4
#define CMD_WORD6   0x1B2050A8

#define MMIO_READ(X) (*((uint32_t volatile*) (X)))
#define MMIO_WRITE(X, V) (*((uint32_t volatile*) (X)) = V)