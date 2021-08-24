
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


#include <handler.h>

__handler__ void test_hh(handler_args_t *args) 
{
    printf("header handler!\n");
}

__handler__ void test_ph(handler_args_t *args) 
{
    uint32_t pkt_id = *((uint32_t*) (args->task->pkt_mem));
    printf("payload handler! pkt_id: 0x%lx\n", pkt_id);

    spin_cmd_t cmd;
    //spin_rdma_put(99, args->task->pkt_mem, args->task->pkt_mem_size, &cmd);
    spin_dma_to_host(0xdeadbeefdeadbeef, 0xcafebebe, 4, 0, &cmd);
}

__handler__ void test_th(handler_args_t *args) 
{
    printf("completion handler!\n");
}

void init_handlers(handler_fn * hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {test_hh, test_ph, test_th};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];
}
