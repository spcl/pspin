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

#ifndef __SPIN_H__
#define __SPIN_H__

#include <stdlib.h>
#include <stdint.h>

#include "spin_hw_conf.h"

#define SPIN_SUCCESS 0
#define SPIN_ERR 1

#ifdef __cplusplus
extern "C" {  
#endif  

typedef uint32_t mem_addr_t;
typedef uint32_t mem_size_t;
typedef uint64_t host_addr_t;

typedef struct spin_ec 
{
    //handler memory
    mem_addr_t handler_mem_addr;
    mem_size_t handler_mem_size;

    //host memory
    host_addr_t host_mem_addr;
    mem_size_t host_mem_size;

    //header handler
    mem_addr_t hh_addr;
    mem_size_t hh_size;

    //payload handler
    mem_addr_t ph_addr;
    mem_size_t ph_size;

    //completion (aka tail) handler
    mem_addr_t th_addr;
    mem_size_t th_size;

    //L1 scratchpads
    mem_addr_t scratchpad_addr[NUM_CLUSTERS];
    mem_size_t scratchpad_size[NUM_CLUSTERS];

} __attribute__((__packed__)) spin_ec_t;

typedef uint32_t spin_nic_addr_t;

int spin_nicmem_write(spin_nic_addr_t addr, void *data, size_t size, void* user_ptr);
int spin_nicmem_read(spin_nic_addr_t addr, void *data, size_t size, void* user_ptr);
int spin_find_handler_by_name(const char *binfile, const char* handler_name, spin_nic_addr_t *handler_addr, size_t *handler_size);

#ifdef __cplusplus  
} // extern "C"  
#endif

#endif /* __SPIN_H__ */