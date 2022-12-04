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

#ifndef HOST
#include <handler.h>
#include <packets.h>
#include <spin_dma.h>
#else
#include <handler_profiler.h>
#endif

#include "synthetic.h"

__handler__ void synthetic_ph(handler_args_t *args)
{
    task_t *task = args->task;
    benchmark_params_t params = *(benchmark_params_t *)task->handler_mem;
    uint32_t hpu_cost = *(uint32_t *)(task->pkt_mem + sizeof(pkt_hdr_t));
    uint32_t acc = 0;
    volatile uint32_t res;

    for (int i = 0; i < hpu_cost; i++)
        acc += i;

    res = acc;
}

void init_handlers(handler_fn * hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {NULL, synthetic_ph, NULL};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];
}
