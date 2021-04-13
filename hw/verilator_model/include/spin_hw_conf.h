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

// WARNING: this has to match pspin_cfg_pkg.sv !!!
#define NUM_CLUSTERS 4
#define NUM_CORES 8
#define C_MSGID_WIDTH 10
#define PCIE_START_ADDR 0x1000000000000000

// 1 MiB
#define L1_CLUSTER_ACTUAL_MEM_SIZE 0x00100000

// 1 KiB reserved at the beginning.
#define L1_RUNTIME_OFFSET 0x00000400

// 16 KiB
#define L1_RUNTIME_SIZE 0x00004000

#define L1_PKT_BUFF_OFFSET (L1_RUNTIME_OFFSET + L1_RUNTIME_SIZE)

// 32 KiB
#define L1_PKT_BUFF_SIZE 0x00008000

#define L2_PKT_BUFF_START 0x1c400000
#define L2_PKT_BUFF_SIZE 4 * 1024 * 1024

#define L1_SCRATCHPAD_OFFSET (L1_PKT_BUFF_OFFSET + L1_PKT_BUFF_SIZE)
#define L1_SCRATCHPAD_SIZE (L1_CLUSTER_ACTUAL_MEM_SIZE - L1_PKT_BUFF_OFFSET)
