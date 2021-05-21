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

//#include <hal/pulp.h>
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#define ECALL_PSPIN_HANDLER_EXIT 0xa

#define PULP_CSR_MSTATUS 0x300
#define PULP_CSR_MTVEC 0x305
#define PULP_CSR_MEPC 0x341
#define PULP_CSR_MCAUSE 0x342
#define PULP_CSR_PRIVLV 0xc10

#define PULP_CSR_PMPCFG0 0x3a0
#define PULP_CSR_PMPCFG1 0x3a1
#define PULP_CSR_PMPCFG2 0x3a2
#define PULP_CSR_PMPCFG3 0x3a3
#define PULP_CSR_PMPADDR0 0x3b0
#define PULP_CSR_PMPADDR1 0x3b1
#define PULP_CSR_PMPADDR2 0x3b2
#define PULP_CSR_PMPADDR3 0x3b3
#define PULP_CSR_PMPADDR4 0x3b4
#define PULP_CSR_PMPADDR5 0x3b5
#define PULP_CSR_PMPADDR6 0x3b6
#define PULP_CSR_PMPADDR7 0x3b7
#define PULP_CSR_PMPADDR8 0x3b8
#define PULP_CSR_PMPADDR9 0x3b9
#define PULP_CSR_PMPADDR10 0x3ba
#define PULP_CSR_PMPADDR11 0x3bb
#define PULP_CSR_PMPADDR12 0x3bc
#define PULP_CSR_PMPADDR13 0x3bd
#define PULP_CSR_PMPADDR14 0x3be
#define PULP_CSR_PMPADDR15 0x3bf

/*
#ifndef NO_PULP
static inline uint32_t rt_core_id()
{
    return hal_core_id();
}

static inline uint32_t rt_cluster_id()
{
    return hal_cluster_id();
}
#endif
*/