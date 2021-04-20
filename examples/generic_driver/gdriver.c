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
#include "gdriver_args.h"
#include "gdriver.h"
#include "packets.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <assert.h>
#include <string.h>

#define SLM_FILES "build/slm_files/"

#define NIC_L2_ADDR 0x1c300000
#define NIC_L2_SIZE (1024 * 1024)

#define HOST_ADDR 0xdeadbeefdeadbeef
#define HOST_SIZE (1024 * 1024 * 1024)

#define SCRATCHPAD_REL_ADDR 0
#define SCRATCHPAD_SIZE (800 * 1024)

#define CHECK_ERR(S)                   \
    {                                  \
        int res;                       \
        if ((res = S) != SPIN_SUCCESS) \
            return res;                \
    }

typedef struct sim_descr
{
    const char *handlers_exe;

    //handler names
    const char *hh_name;
    const char *ph_name;
    const char *th_name;

    //packet generator
    uint32_t num_messages;
    uint32_t num_packets;
    uint32_t packet_size;
    uint32_t packet_delay;
    uint32_t message_delay;

    //L2
    uint32_t handler_mem_addr;
    uint32_t handler_mem_size;

    //L1
    uint32_t scratchpad_addr[NUM_CLUSTERS];
    uint32_t scratchpad_size[NUM_CLUSTERS];

    //host memory
    uint64_t host_mem_addr;
    uint64_t host_mem_size;

    spin_ec_t ec;

    fill_packet_fun_t pkt_fill_fun;
    void *l2_img_to_copy;
    size_t l2_img_to_copy_size;

} sim_descr_t;

static sim_descr_t sim_state;

void pcie_mst_write_complete(void *user_ptr);

int make_ec()
{
    spin_nic_addr_t hh_addr = 0, ph_addr = 0, th_addr = 0;
    size_t hh_size = 0, ph_size = 0, th_size = 0;

    if (sim_state.hh_name != NULL) 
    {
        CHECK_ERR(spin_find_handler_by_name(sim_state.handlers_exe, sim_state.hh_name, &hh_addr, &hh_size));
    }

    if (sim_state.ph_name != NULL) 
    {
        CHECK_ERR(spin_find_handler_by_name(sim_state.handlers_exe, sim_state.ph_name, &ph_addr, &ph_size));
    }

    if (sim_state.th_name != NULL) 
    {
        CHECK_ERR(spin_find_handler_by_name(sim_state.handlers_exe, sim_state.th_name, &th_addr, &th_size));
    }

    printf("hh_addr: %x; hh_size: %lu;\n", hh_addr, hh_size);
    printf("ph_addr: %x; ph_size: %lu;\n", ph_addr, ph_size);
    printf("th_addr: %x; th_size: %lu;\n", th_addr, th_size);

    sim_state.ec.handler_mem_addr = sim_state.handler_mem_addr;
    sim_state.ec.handler_mem_size = sim_state.handler_mem_size;
    sim_state.ec.host_mem_addr = sim_state.host_mem_addr;
    sim_state.ec.host_mem_size = sim_state.host_mem_size;
    sim_state.ec.hh_addr = hh_addr;
    sim_state.ec.ph_addr = ph_addr;
    sim_state.ec.th_addr = th_addr;
    sim_state.ec.hh_size = hh_size;
    sim_state.ec.ph_size = ph_size;
    sim_state.ec.th_size = th_size;

    for (int i = 0; i < NUM_CLUSTERS; i++)
    {
        sim_state.ec.scratchpad_addr[i] = sim_state.scratchpad_addr[i];
        sim_state.ec.scratchpad_size[i] = sim_state.scratchpad_size[i];
    }
}

void generate_packets()
{
    spin_ec_t ec;

    uint8_t *pkt_buff = (uint8_t *)malloc(sizeof(uint8_t) * (sim_state.packet_size));
    assert(pkt_buff != NULL);

    for (uint32_t msg_idx = 0; msg_idx < sim_state.num_messages; msg_idx++)
    {
        for (uint32_t pkt_idx = 0; pkt_idx < sim_state.num_packets; pkt_idx++)
        {
            uint32_t pkt_size = sim_state.packet_size;
            uint32_t l1_pkt_size = pkt_size;

            if (sim_state.pkt_fill_fun != NULL)
            {
                pkt_size = sim_state.pkt_fill_fun(msg_idx, pkt_idx, pkt_buff, sim_state.packet_size, &l1_pkt_size);
            }
            else
            {
                // generate IP+UDP headers
                pkt_hdr_t *hdr = (pkt_hdr_t*) pkt_buff;
                hdr->ip_hdr.ihl = 5;
                hdr->ip_hdr.length = pkt_size;
                // TODO: set other fields
            }

            bool is_last = (pkt_idx + 1 == sim_state.num_packets);
            uint32_t delay = (is_last) ? sim_state.message_delay : sim_state.packet_delay;
            pspinsim_packet_add(&(sim_state.ec), msg_idx, pkt_buff, pkt_size, l1_pkt_size, is_last, delay, 0);
        }
    }

    pspinsim_packet_eos();

    free(pkt_buff);
}

void pcie_mst_write_complete(void *user_ptr)
{
    printf("Write to NIC memory completed (user_ptr: %p)\n", user_ptr);
    generate_packets();
}

/*** interface ***/

int gdriver_set_packet_fill_callback(fill_packet_fun_t pkt_fill_fun)
{
    sim_state.pkt_fill_fun = pkt_fill_fun;
    return GDRIVER_OK;
}

int gdriver_set_l2_img(void *img, size_t size)
{
    sim_state.l2_img_to_copy = img;
    sim_state.l2_img_to_copy_size = size;
    return GDRIVER_OK;
}

int gdriver_init(int argc, char **argv, const char *hfile, const char *hh, const char *ph, const char *th)
{
    struct gengetopt_args_info ai;
    pspin_conf_t conf;

    if (cmdline_parser(argc, argv, &ai) != 0)
    {
        return GDRIVER_ERR;
    }

    pspinsim_default_conf(&conf);
    conf.slm_files_path = SLM_FILES;

    pspinsim_init(argc, argv, &conf);

    pspinsim_cb_set_pcie_mst_write_completion(pcie_mst_write_complete);

    memset(&sim_state, 0, sizeof(sim_state));

    sim_state.handlers_exe = hfile;
    sim_state.hh_name = hh;
    sim_state.ph_name = ph;
    sim_state.th_name = th;
    sim_state.num_messages = ai.num_messages_arg;
    sim_state.num_packets = ai.num_packets_arg;
    sim_state.packet_size = ai.packet_size_arg;
    sim_state.packet_delay = ai.packet_delay_arg;
    sim_state.message_delay = ai.message_delay_arg;
    sim_state.handler_mem_addr = NIC_L2_ADDR;
    sim_state.handler_mem_size = NIC_L2_SIZE;
    sim_state.host_mem_addr = HOST_ADDR;
    sim_state.host_mem_size = HOST_SIZE;

    sim_state.scratchpad_addr[NUM_CLUSTERS];
    sim_state.scratchpad_size[NUM_CLUSTERS];

    for (int i = 0; i < NUM_CLUSTERS; i++)
    {
        sim_state.scratchpad_addr[i] = SCRATCHPAD_REL_ADDR;
        sim_state.scratchpad_size[i] = SCRATCHPAD_SIZE;
    }

    make_ec();

    return GDRIVER_OK;
}

int gdriver_run()
{
    if (sim_state.l2_img_to_copy != NULL)
    {
        spin_nic_addr_t dest = sim_state.handler_mem_addr;
        uint32_t dest_capacity = sim_state.handler_mem_size;
        void *src = sim_state.l2_img_to_copy;
        spin_nic_addr_t src_size = sim_state.l2_img_to_copy_size;

        assert(src_size <= dest_capacity);
        printf("Copying %d bytes to %x (src: %p)\n", src_size, dest, src);
        spin_nicmem_write(dest, (void *)src, src_size, (void *)0);
    }
    else
    {
        generate_packets();
    }

    if (pspinsim_run() == SPIN_SUCCESS)
        return GDRIVER_OK;
    else
        return GDRIVER_ERR;
}

int gdriver_fini()
{
    if (pspinsim_fini() == SPIN_SUCCESS)
        return GDRIVER_OK;
    return GDRIVER_ERR;
}
