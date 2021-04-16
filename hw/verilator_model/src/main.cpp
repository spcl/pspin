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

#include "pspinsim.h"
#include "spin.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

//this is where the runtime SLM files are (they are flashed to L2)
#define SLM_FILES_PATH "build/slm_files/"
#define PKT_TASK_FILE "../sim_files/tasks.csv"
#define PKT_DATA_FILE "../sim_files/data.bin"

void pkt_out(uint8_t* data, size_t len)
{
    printf("Got packet! (len: %lu)\n", len);
}

void pcie_slv_write(uint64_t addr, uint8_t* data, size_t len)
{
    printf("NIC wants to write %lu bytes to addr %lx\n", len, addr);
}

void pcie_slv_read(uint64_t addr, uint8_t* data, size_t len)
{
    printf("NIC wants to read %lu bytes from addr %lx\n", len, addr);
}

void pcie_mst_write_complete(void *user_ptr)
{
    printf("Write to NIC memory completed (user_ptr: %p)\n", user_ptr);
}

void pcie_mst_read_complete(void *user_ptr)
{
    printf("Read from NIC memory completed (user_ptr: %p)\n", user_ptr);
}

int main(int argc, char**argv)
{
    pspin_conf_t conf;
    pspinsim_default_conf(&conf);
    conf.slm_files_path = (char*) SLM_FILES_PATH;

    pspinsim_init(argc, argv, &conf);

    pspinsim_cb_set_pkt_out(pkt_out);
    pspinsim_cb_set_pcie_slv_write(pcie_slv_write);
    pspinsim_cb_set_pcie_slv_read(pcie_slv_read);
    pspinsim_cb_set_pcie_mst_write_completion(pcie_mst_write_complete);
    pspinsim_cb_set_pcie_mst_read_completion(pcie_mst_read_complete);

    int ret = pspinsim_packet_trace_read(PKT_TASK_FILE, PKT_DATA_FILE);
    if (ret!=SPIN_SUCCESS) {
        printf("Error while reading packet trace!\n");
        exit(1);
    }

    pspinsim_packet_eos();
    
    pspinsim_run();

    pspinsim_fini();

    return 0;
}
