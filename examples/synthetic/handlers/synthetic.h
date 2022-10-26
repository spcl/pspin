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

typedef struct benchmark_params
{
    /* Workload 1: Computations in handler */
    int loop_spin_count;

    /* Workload 2: Write packet payload (DMA) to host */
    uint32_t dma_to_size;
    int dma_to_count;

    /* Workload 3: Read data (DMA) from host and send to the network */
    uint32_t dma_from_size;
    int dma_from_count;
} benchmark_params_t;
