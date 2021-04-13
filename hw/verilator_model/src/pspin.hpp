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

#include <stdint.h>

#include "spin.h"
#include "spin_hw_conf.h"

#define THROUGHPUT_1GHZ(T, S) (((double)8 * S) / T)

#define NI_CTRL_PORT_ASSIGN(SRC, SRC_PREFIX, DST)                                                             \
    {                                                                                                         \
        (DST)->her_ready_i = &((SRC)->EVALUATOR(SRC_PREFIX, ready_o));                                        \
        (DST)->her_valid_o = &((SRC)->EVALUATOR(SRC_PREFIX, valid_i));                                        \
        (DST)->her_o.msgid = &((SRC)->EVALUATOR(SRC_PREFIX, msgid_i));                                        \
        (DST)->her_o.eom = &((SRC)->EVALUATOR(SRC_PREFIX, is_eom_i));                                         \
        (DST)->her_o.her_addr = &((SRC)->EVALUATOR(SRC_PREFIX, addr_i));                                      \
        (DST)->her_o.her_size = &((SRC)->EVALUATOR(SRC_PREFIX, size_i));                                      \
        (DST)->her_o.her_size = &((SRC)->EVALUATOR(SRC_PREFIX, size_i));                                      \
        (DST)->her_o.xfer_size = &((SRC)->EVALUATOR(SRC_PREFIX, xfer_size_i));                                \
        (DST)->her_o.mpq_meta.handler_mem_addr = &((SRC)->EVALUATOR(SRC_PREFIX, meta_handler_mem_addr_i));    \
        (DST)->her_o.mpq_meta.handler_mem_size = &((SRC)->EVALUATOR(SRC_PREFIX, meta_handler_mem_size_i));    \
        (DST)->her_o.mpq_meta.host_mem_addr = &((SRC)->EVALUATOR(SRC_PREFIX, meta_host_mem_addr_i));          \
        (DST)->her_o.mpq_meta.host_mem_size = &((SRC)->EVALUATOR(SRC_PREFIX, meta_host_mem_size_i));          \
        (DST)->her_o.mpq_meta.hh_addr = &((SRC)->EVALUATOR(SRC_PREFIX, meta_hh_addr_i));                      \
        (DST)->her_o.mpq_meta.hh_size = &((SRC)->EVALUATOR(SRC_PREFIX, meta_hh_size_i));                      \
        (DST)->her_o.mpq_meta.ph_addr = &((SRC)->EVALUATOR(SRC_PREFIX, meta_ph_addr_i));                      \
        (DST)->her_o.mpq_meta.ph_size = &((SRC)->EVALUATOR(SRC_PREFIX, meta_ph_size_i));                      \
        (DST)->her_o.mpq_meta.th_addr = &((SRC)->EVALUATOR(SRC_PREFIX, meta_th_addr_i));                      \
        (DST)->her_o.mpq_meta.th_size = &((SRC)->EVALUATOR(SRC_PREFIX, meta_th_size_i));                      \
        (DST)->her_o.mpq_meta.scratchpad_addr[0] = &((SRC)->EVALUATOR(SRC_PREFIX, meta_scratchpad_0_addr_i)); \
        (DST)->her_o.mpq_meta.scratchpad_size[0] = &((SRC)->EVALUATOR(SRC_PREFIX, meta_scratchpad_0_size_i)); \
        (DST)->her_o.mpq_meta.scratchpad_addr[1] = &((SRC)->EVALUATOR(SRC_PREFIX, meta_scratchpad_1_addr_i)); \
        (DST)->her_o.mpq_meta.scratchpad_size[1] = &((SRC)->EVALUATOR(SRC_PREFIX, meta_scratchpad_1_size_i)); \
        (DST)->her_o.mpq_meta.scratchpad_addr[2] = &((SRC)->EVALUATOR(SRC_PREFIX, meta_scratchpad_2_addr_i)); \
        (DST)->her_o.mpq_meta.scratchpad_size[2] = &((SRC)->EVALUATOR(SRC_PREFIX, meta_scratchpad_2_size_i)); \
        (DST)->her_o.mpq_meta.scratchpad_addr[3] = &((SRC)->EVALUATOR(SRC_PREFIX, meta_scratchpad_3_addr_i)); \
        (DST)->her_o.mpq_meta.scratchpad_size[3] = &((SRC)->EVALUATOR(SRC_PREFIX, meta_scratchpad_3_size_i)); \
        (DST)->pspin_active_i = &tb->pspin_active_o;                                                          \
        (DST)->feedback_valid_i = &tb->feedback_valid_o;                                                      \
        (DST)->feedback_ready_o = &tb->feedback_ready_i;                                                      \
        (DST)->feedback_msgid_i = &tb->feedback_msgid_o;                                                      \
        (DST)->feedback_her_addr_i = &tb->feedback_her_addr_o;                                                \
        (DST)->feedback_her_size_i = &tb->feedback_her_size_o;                                                \
        (DST)->eos_o = &tb->eos_i;                                                                            \
    }

#define NO_CMD_PORT_ASSIGN(SRC, SRC_PREFIX, DST)                                        \
    {                                                                                   \
        (DST)->no_cmd_req_ready_o = &((SRC)->EVALUATOR(SRC_PREFIX, req_ready_i));       \
        (DST)->no_cmd_req_valid_i = &((SRC)->EVALUATOR(SRC_PREFIX, req_valid_o));       \
        (DST)->no_cmd_req_src_addr_i = &((SRC)->EVALUATOR(SRC_PREFIX, req_src_addr_o)); \
        (DST)->no_cmd_req_length_i = &((SRC)->EVALUATOR(SRC_PREFIX, req_length_o));     \
        (DST)->no_cmd_req_user_ptr_i = &((SRC)->EVALUATOR(SRC_PREFIX, req_user_ptr_o)); \
        (DST)->no_cmd_req_id_i = &((SRC)->EVALUATOR(SRC_PREFIX, req_id_o));             \
        (DST)->no_cmd_req_nid_i = &((SRC)->EVALUATOR(SRC_PREFIX, req_nid_o));           \
        (DST)->no_cmd_req_fid_i = &((SRC)->EVALUATOR(SRC_PREFIX, req_fid_o));           \
        (DST)->no_cmd_resp_valid_o = &((SRC)->EVALUATOR(SRC_PREFIX, resp_valid_i));     \
        (DST)->no_cmd_resp_id_o = &((SRC)->EVALUATOR(SRC_PREFIX, resp_id_i));           \
    }

namespace PsPIN
{

    typedef spin_ec_t mpq_meta_t;
 
    typedef struct her_descr
    {
        uint32_t msgid;
        uint8_t eom;

        //full her descriptor
        mem_addr_t her_addr;
        mem_size_t her_size;
        mem_size_t xfer_size;

        mpq_meta_t mpq_meta;

        //Note: this is used only between the driver and the NIC inbound engine. It 
        //is not sent to PsPIN. 
        uint64_t user_ptr;
        uint64_t nic_arrival_time;
    } __attribute__((__packed__)) her_descr_t;

    typedef struct mpq_meta_p
    {
        //handler memory
        mem_addr_t *handler_mem_addr;
        mem_size_t *handler_mem_size;

        //host memory
        host_addr_t *host_mem_addr;
        mem_size_t *host_mem_size;

        //header handler
        mem_addr_t *hh_addr;
        mem_size_t *hh_size;

        //payload handler
        mem_addr_t *ph_addr;
        mem_size_t *ph_size;

        //completion (aka tail) handler
        mem_addr_t *th_addr;
        mem_size_t *th_size;

        //L1 scratchpads
        mem_addr_t *scratchpad_addr[NUM_CLUSTERS];
        mem_size_t *scratchpad_size[NUM_CLUSTERS];

    } __attribute__((__packed__)) mpq_meta_p_t;

    typedef struct her_descr_p
    {
        uint16_t *msgid;
        uint8_t *eom;

        //full her descriptor
        mem_addr_t *her_addr;
        mem_size_t *her_size;
        mem_size_t *xfer_size;

        mpq_meta_p_t mpq_meta;
    } __attribute__((__packed__)) her_descr_p_t;

    typedef struct ni_control_port
    {
        uint8_t *her_valid_o;
        uint8_t *her_ready_i;
        her_descr_p_t her_o;
        uint8_t *pspin_active_i;
        uint8_t *feedback_valid_i;
        uint8_t *feedback_ready_o;
        uint16_t *feedback_msgid_i;
        uint32_t *feedback_her_addr_i;
        uint32_t *feedback_her_size_i;
        uint8_t *eos_o;
    } ni_control_port_t;

    typedef struct no_cmd_port
    {
        // Request
        uint8_t *no_cmd_req_ready_o;
        uint8_t *no_cmd_req_valid_i;
        uint64_t *no_cmd_req_src_addr_i;
        uint32_t *no_cmd_req_length_i;
        uint64_t *no_cmd_req_user_ptr_i;
        uint8_t *no_cmd_req_id_i;
        uint32_t *no_cmd_req_nid_i;
        uint32_t *no_cmd_req_fid_i;

        // Response
        uint8_t *no_cmd_resp_valid_o;
        uint8_t *no_cmd_resp_id_o;
    } no_cmd_port_t;

} // namespace PsPIN
