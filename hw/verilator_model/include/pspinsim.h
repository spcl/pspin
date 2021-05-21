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

#ifndef __PSPINSIM_H__
#define __PSPINSIM_H__

#include "spin.h"

#ifdef __cplusplus
extern "C" {  
#endif  

typedef struct ni_conf
{
    uint32_t axi_aw_buffer;
    uint32_t axi_w_buffer;
    uint32_t axi_b_buffer;
} ni_conf_t;

typedef struct no_conf
{
    uint32_t axi_ar_buffer;
    uint32_t axi_r_buffer;
    double   network_G;
    uint32_t max_pkt_size;
    uint32_t max_network_queue_len;
} no_conf_t;

typedef struct pcie_slv_conf
{
    uint32_t axi_aw_buffer;
    uint32_t axi_w_buffer;
    uint32_t axi_ar_buffer;
    uint32_t axi_b_buffer;
    uint32_t axi_r_buffer;
    uint32_t pcie_L;
    double   pcie_G;
} pcie_slv_conf_t;

typedef struct pspin_conf {
    const char *slm_files_path;
    ni_conf_t ni_conf;
    no_conf_t no_conf;
    pcie_slv_conf_t pcie_slv_conf;
} pspin_conf_t;

typedef void (*pkt_out_cb_t)(uint8_t*, size_t);
typedef void (*pkt_feedback_cb_t)(uint64_t, uint64_t, uint64_t, uint64_t);
typedef void (*pcie_slv_write_cb_t)(uint64_t, uint8_t*, size_t);
typedef void (*pcie_slv_read_cb_t)(uint64_t, uint8_t*, size_t);
typedef void (*pcie_mst_write_cb_t)(void*);
typedef void (*pcie_mst_read_cb_t)(void*);

int pspinsim_default_conf(pspin_conf_t *conf);

int pspinsim_init(int argc, char **argv, pspin_conf_t *conf);
int pspinsim_run();
int pspinsim_run_tick(uint8_t *done_flag);
int pspinsim_fini();

int pspinsim_packet_trace_read(const char* pkt_file_path, const char* data_file_path);
int pspinsim_packet_add(spin_ec_t* ec, uint32_t msgid, uint8_t* pkt_data, size_t pkt_len, size_t pkt_l1_len, uint8_t eom, uint32_t wait_cycles, uint64_t user_ptr);
int pspinsim_packet_eos();

int pspinsim_cb_set_pkt_out(pkt_out_cb_t cb);
int pspinsim_cb_set_pcie_slv_write(pcie_slv_write_cb_t cb);
int pspinsim_cb_set_pcie_slv_read(pcie_slv_read_cb_t cb);
int pspinsim_cb_set_pcie_mst_write_completion(pcie_mst_write_cb_t cb);
int pspinsim_cb_set_pcie_mst_read_completion(pcie_mst_read_cb_t cb);
int pspinsim_cb_set_pkt_feedback(pkt_feedback_cb_t cb);

#ifdef __cplusplus  
} // extern "C"  
#endif

#endif /* __PSPINSIM_H__ */
