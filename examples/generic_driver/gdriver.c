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

#include "pspinsim.h"
#include "spin.h"
#include "gdriver_args.h"
#include "gdriver.h"
#include "packets.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include <string.h>

#define SLM_FILES "build/slm_files/"

#define MAGIC_PATH "NULL"

#define EC_MAX_NUM 2

#define NIC_L2_ADDR 0x1c300000
#define NIC_L2_SIZE (1024 * 1024)
#define NIC_L2_EC_CHUNK_SIZE (NIC_L2_SIZE / EC_MAX_NUM)

#define HOST_ADDR 0xdeadbeefdeadbeef
#define HOST_SIZE (1024 * 1024 * 1024)
#define HOST_EC_CHUNK_SIZE (HOST_SIZE / EC_MAX_NUM)

#define SCRATCHPAD_REL_ADDR 0
#define SCRATCHPAD_SIZE (800 * 1024)
#define SCRATCHPAD_EC_CHUNK_SIZE (SCRATCHPAD_SIZE / EC_MAX_NUM)

#define EC_MEM_BASE_ADDR(generic_ectx_id, base, chunk_size) \
    (base + (generic_ectx_id * chunk_size))

#define CHECK_ERR(S)                   \
    {                                  \
        int res;                       \
        if ((res = S) != SPIN_SUCCESS) \
            return res;                \
    }

typedef struct gdriver_ttrace
{
    char *trace_path;
    uint32_t packets_parsed;
    match_packet_fun_t matching_cb;
} gdriver_ttrace_t;

typedef struct gdriver_tgen
{
    uint32_t num_messages;
    uint32_t num_packets;
    uint32_t packet_size;
    uint32_t packet_delay;
    uint32_t message_delay;
    uint32_t packets_sent;
} gdriver_tgen_t;

typedef struct gdriver_ectx
{
    spin_ec_t ectx;
    fill_packet_fun_t pkt_fill_cb;
    char matching_ctx[GDRIVER_MATCHING_CTX_MAXSIZE];
} gdriver_ectx_t;

typedef struct gdriver_sim_descr
{
    int num_ectxs;
    gdriver_ectx_t ectxs[EC_MAX_NUM];

    int is_trace;
    gdriver_ttrace_t ttrace;
    gdriver_tgen_t tgen;

    uint32_t packets_processed;
} gdriver_sim_descr_t;

static gdriver_sim_descr_t sim_state;

static void gdriver_dump_ectx_info(const gdriver_ectx_t *gectx)
{
    printf("[GDRIVER] gectx=%p info:\n", gectx);
    printf("[GDRIVER] hh_addr=%x; hh_size=%u;\n",
        gectx->ectx.hh_addr, gectx->ectx.hh_size);
    printf("[GDRIVER] ph_addr=%x; ph_size=%u;\n",
        gectx->ectx.ph_addr, gectx->ectx.ph_size);
    printf("[GDRIVER] th_addr=%x; th_size=%u;\n",
        gectx->ectx.th_addr, gectx->ectx.th_size);
    printf("[GDRIVER] handler_mem_addr=%x; handler_mem_size=%u\n",
        gectx->ectx.handler_mem_addr, gectx->ectx.handler_mem_size);
    printf("[GDRIVER] host_mem_addr=%lx; host_mem_size=%u\n",
        gectx->ectx.host_mem_addr, gectx->ectx.host_mem_size);
    printf("[GDRIVER] matching context=%s\n", gectx->matching_ctx ? gectx->matching_ctx : "NULL");
}

static void gdriver_fill_pkt(int ectx_idx, uint32_t msg_idx, void *data,
    uint8_t *pkt_buf, uint32_t pkt_size, uint32_t *l1_pkt_size)
{
    pkt_hdr_t *hdr;

    if (sim_state.ectxs[ectx_idx].pkt_fill_cb != NULL) {
        pkt_size = sim_state.ectxs[ectx_idx].pkt_fill_cb(
            msg_idx, data, pkt_buf, pkt_size, l1_pkt_size);
    } else {
        // generate IP+UDP headers
        hdr = (pkt_hdr_t*)pkt_buf;
        hdr->ip_hdr.ihl = 5;
        hdr->ip_hdr.length = pkt_size;
        *l1_pkt_size = pkt_size;
        // TODO: set other fields
    }
}

static void gdriver_generate_packets()
{
    uint32_t global_msg_counter = 0, global_packet_counter = 0;
    uint8_t *pkt_buf;
    uint32_t pkt_size, l1_pkt_size, delay;
    int is_last;

    printf("[GDRIVER]: Using default packet generator\n");

    pkt_buf = (uint8_t *)malloc(sizeof(uint8_t) * (sim_state.tgen.packet_size));
    assert(pkt_buf != NULL);

    for (int ectx_idx = 0; ectx_idx < sim_state.num_ectxs; ectx_idx++) {
        for (uint32_t msg_idx = 0; msg_idx < sim_state.tgen.num_messages; msg_idx++) {
            for (uint32_t pkt_idx = 0; pkt_idx < sim_state.tgen.num_packets; pkt_idx++) {
                pkt_size = sim_state.tgen.packet_size;

                gdriver_fill_pkt(ectx_idx, ectx_idx, (void *)&pkt_idx,
                    pkt_buf, pkt_size, &l1_pkt_size);
                is_last = (pkt_idx + 1 == sim_state.tgen.num_packets);
                delay = (is_last) ? sim_state.tgen.message_delay : sim_state.tgen.packet_delay;

                pspinsim_packet_add(&(sim_state.ectxs[ectx_idx].ectx), ectx_idx,
                    pkt_buf, pkt_size, l1_pkt_size, is_last, delay, 0);

                sim_state.tgen.packets_sent++;
                global_packet_counter++;
            }
            global_msg_counter++;
        }
    }

    pspinsim_packet_eos();

    free(pkt_buf);
}

static void gdriver_parse_trace()
{
    uint32_t nsources, npackets, max_pkt_size;
    uint32_t msgid, pkt_id, hpu, dmaw, dmar, outbound;
    uint32_t pkt_size, ipg, wait_cycles, l1_pkt_size;
    char src_addr[GDRIVER_MATCHING_CTX_MAXSIZE];
    char dst_addr[GDRIVER_MATCHING_CTX_MAXSIZE];
    uint8_t *pkt_buf;
    int is_last, matched, ret, ectx_id;

    FILE *trace_file = fopen(sim_state.ttrace.trace_path, "r");
    assert(trace_file);
    printf("[GDRIVER]: Packet trace path: %s\n", sim_state.ttrace.trace_path);

    /* Parse trace header */
    ret = fscanf(trace_file, "%u %u %u\n", &nsources, &npackets, &max_pkt_size);
    assert(nsources > 0 && nsources <= sim_state.num_ectxs);
    assert(npackets > 0);

    /* TODO: remove me from traces */
    for (int i = 0; i < nsources; i++)
        fscanf(trace_file, "%s %u %u %u %u %u\n",
            src_addr, &pkt_size, &msgid, &hpu, &dmaw, &dmar);

    pkt_buf = (uint8_t *)malloc(sizeof(uint8_t) * max_pkt_size);
    assert(pkt_buf != NULL);

    sim_state.ttrace.packets_parsed = 0;
    wait_cycles = 0;
    while (!feof(trace_file)) {
        /* TODO/FIXME: for now dmaw/dmar/outbound are useless */
        ret = fscanf(trace_file, "%s %s %u %u %u %d %u %u %u %u\n",
            src_addr, dst_addr, &pkt_size, &msgid, &pkt_id,
            &is_last, &hpu, &dmaw, &dmar, &outbound);
        assert(ret == 10);

        /* FIXME: here we stupidly assume that we can mask FMQs bits */
        msgid = msgid & 1111;

        printf("%s %s %u %u %d %u\n", src_addr, dst_addr, pkt_size, msgid, is_last, hpu);

        /* FIXME: we'll probably will not have IPGs */
        //if (pkt_size == 0) {
        //    assert(wait_cycles == 0);
        //    assert(ipg > 0);
        //    wait_cycles = ipg;
        //} else {
        //    assert(ipg == 0);

        matched = 0;
        for (ectx_id = 0; ectx_id < sim_state.num_ectxs; ectx_id++) {
            if (sim_state.ttrace.matching_cb(
                src_addr, sim_state.ectxs[ectx_id].matching_ctx)) {
                matched = 1;
                break;
            }
        }

        assert(matched);

        gdriver_fill_pkt(ectx_id, msgid, (void *)&hpu, pkt_buf, pkt_size, &l1_pkt_size);
        pspinsim_packet_add(&(sim_state.ectxs[ectx_id].ectx), msgid,
            pkt_buf, pkt_size, l1_pkt_size, is_last, wait_cycles, ectx_id);

        sim_state.ttrace.packets_parsed++;
    }

    assert(sim_state.ttrace.packets_parsed == npackets);

    fclose(trace_file);
    free(pkt_buf);

    pspinsim_packet_eos();
}

static void gdriver_pcie_mst_write_complete(void *user_ptr)
{
    printf("Write to NIC memory completed (user_ptr: %p)\n", user_ptr);
}

static void gdriver_feedback(uint64_t user_ptr, uint64_t her_addr,
    uint64_t nic_arrival_time, uint64_t pspin_arrival_time, uint64_t feedback_time)
{
    if (sim_state.ttrace.matching_cb) {
        printf("[BMARK]: "
               "ectx=%u "
               "her=0x%x "
               "nic_arrival_time=%lu "
               "pspin_arrival_time=%lu "
               "feedback_time=%lu\n",
               (uint32_t)user_ptr + 1,
               (uint32_t)her_addr,
               nic_arrival_time,
               pspin_arrival_time,
               feedback_time);
    }

    sim_state.packets_processed++;
}

static int gdriver_init_ectx(gdriver_ectx_t *gectx, uint32_t gectx_id,
    const char *handlers_exe, const char *hh_name,
    const char *ph_name, const char *th_name,
    fill_packet_fun_t fill_cb, void *l2_img, size_t l2_img_size,
    void *matching_ctx, size_t matching_ctx_size)
{
    spin_nic_addr_t hh_addr = 0, ph_addr = 0, th_addr = 0;
    size_t hh_size = 0, ph_size = 0, th_size = 0;

    if ((hh_name == NULL) && (ph_name == NULL) && (th_name == NULL))
        return GDRIVER_ERR;

    if (hh_name != NULL)
        CHECK_ERR(spin_find_handler_by_name(handlers_exe, hh_name, &hh_addr, &hh_size));

    if (ph_name != NULL)
        CHECK_ERR(spin_find_handler_by_name(handlers_exe, ph_name, &ph_addr, &ph_size));

    if (th_name != NULL)
        CHECK_ERR(spin_find_handler_by_name(handlers_exe, th_name, &th_addr, &th_size));

    gectx->ectx.hh_addr = hh_addr;
    gectx->ectx.ph_addr = ph_addr;
    gectx->ectx.th_addr = th_addr;
    gectx->ectx.hh_size = hh_size;
    gectx->ectx.ph_size = ph_size;
    gectx->ectx.th_size = th_size;

    /*
     * For now assume that each execution context had its own region of host/L1/L2
     * memories.
     *
     * See EC_MEM_BASE_ADDR macro definition for clarity.
     */

    gectx->ectx.handler_mem_addr = EC_MEM_BASE_ADDR(gectx_id,
        NIC_L2_ADDR, NIC_L2_EC_CHUNK_SIZE);
    gectx->ectx.handler_mem_size = NIC_L2_EC_CHUNK_SIZE;
    assert(gectx->ectx.handler_mem_addr < (NIC_L2_ADDR + NIC_L2_SIZE));

    gectx->ectx.host_mem_addr = EC_MEM_BASE_ADDR(gectx_id,
        HOST_ADDR, HOST_EC_CHUNK_SIZE);
    gectx->ectx.host_mem_size = HOST_EC_CHUNK_SIZE;
    assert(gectx->ectx.host_mem_addr < (HOST_ADDR + HOST_SIZE));

    for (int i = 0; i < NUM_CLUSTERS; i++) {
        gectx->ectx.scratchpad_addr[i] = EC_MEM_BASE_ADDR(gectx_id,
            SCRATCHPAD_REL_ADDR, SCRATCHPAD_EC_CHUNK_SIZE);
        gectx->ectx.scratchpad_size[i] = SCRATCHPAD_EC_CHUNK_SIZE;
        assert(gectx->ectx.scratchpad_addr[i] < (SCRATCHPAD_REL_ADDR + SCRATCHPAD_SIZE));
    }

    gectx->pkt_fill_cb = fill_cb;

    if (l2_img) {
        assert(l2_img_size <= gectx->ectx.handler_mem_size);
        spin_nicmem_write(gectx->ectx.handler_mem_addr,
            (void *)l2_img, l2_img_size, (void *)0);
    }

    if (matching_ctx)
        strcpy(gectx->matching_ctx, matching_ctx);

    gdriver_dump_ectx_info(gectx);

    return GDRIVER_OK;
}

int gdriver_add_ectx(const char *hfile, const char *hh, const char *ph, const char *th,
     fill_packet_fun_t fill_pkt_cb, void *l2_img, size_t l2_img_size,
     void *matching_ctx, size_t matching_ctx_size)
{
    int ret;

    if (sim_state.num_ectxs == EC_MAX_NUM)
        return GDRIVER_ERR;

    if (matching_ctx_size > GDRIVER_MATCHING_CTX_MAXSIZE)
        return GDRIVER_ERR;

    if (gdriver_init_ectx(
        &(sim_state.ectxs[sim_state.num_ectxs]), sim_state.num_ectxs,
        hfile, hh, ph, th,
        fill_pkt_cb, l2_img, l2_img_size,
        matching_ctx, matching_ctx_size)) {
        return GDRIVER_ERR;
    }

    sim_state.num_ectxs++;

    return GDRIVER_OK;
}

int gdriver_run()
{
    if (sim_state.is_trace) {
        gdriver_parse_trace();
    } else {
        gdriver_generate_packets();
    }

    if (pspinsim_run() == SPIN_SUCCESS) {
        return GDRIVER_OK;
    } else {
        return GDRIVER_ERR;
    }
}

int gdriver_fini()
{
    if (pspinsim_fini() != SPIN_SUCCESS)
        return GDRIVER_ERR;

    if (sim_state.is_trace && sim_state.ttrace.packets_parsed != sim_state.packets_processed)
        return GDRIVER_ERR;

    else if (sim_state.tgen.packets_sent != sim_state.packets_processed)
        return GDRIVER_ERR;

    return GDRIVER_OK;
}

int gdriver_init(int argc, char **argv, match_packet_fun_t matching_cb, int *ectx_num)
{
    struct gengetopt_args_info ai;
    pspin_conf_t conf;

    *ectx_num = -1;

    if (cmdline_parser(argc, argv, &ai) != 0)
        return GDRIVER_ERR;

    pspinsim_default_conf(&conf);
    conf.slm_files_path = SLM_FILES;

    pspinsim_init(argc, argv, &conf);

    pspinsim_cb_set_pcie_mst_write_completion(gdriver_pcie_mst_write_complete);
    pspinsim_cb_set_pkt_feedback(gdriver_feedback);

    memset(&sim_state, 0, sizeof(sim_state));

    if (strcmp(ai.trace_file_arg, MAGIC_PATH)) {
        sim_state.is_trace = 1;
        sim_state.ttrace.trace_path = ai.trace_file_arg;
        sim_state.ttrace.matching_cb = matching_cb;
    } else {
        sim_state.tgen.num_messages = ai.num_messages_arg;
        sim_state.tgen.num_packets = ai.num_packets_arg;
        sim_state.tgen.packet_size = ai.packet_size_arg;
        sim_state.tgen.packet_delay = ai.packet_delay_arg;
        sim_state.tgen.message_delay = ai.message_delay_arg;
        sim_state.ttrace.matching_cb = NULL;
    }

    *ectx_num = EC_MAX_NUM;

    return GDRIVER_OK;
}
