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

#include "AXIPort.hpp"
#include <stdint.h>
#include <queue>
#include <unordered_map>
#include <functional>
#include <assert.h>
#include "pspin.hpp"
#include "spin.h"
#include "SimModule.hpp"

namespace PsPIN
{
    class NOSlave: public SimModule
    {
    public:
        typedef uint8_t cmd_id_t;
        class NICCommand 
        {
            public:
                uint64_t source_addr;
                uint32_t length;
                uint32_t sput_length;
                uint32_t nid;
                uint32_t fid;
                cmd_id_t cmd_id;
        };

        typedef std::function<void(NICCommand)> NICCommandCallback;

    private:
        no_cmd_port &no_cmd;
        uint32_t total_cmds;
        bool block_cmds;
        NICCommandCallback command_cb;

        std::queue<cmd_id_t> response_queue;

    public:
        NOSlave(no_cmd_port_t &no_cmd) 
        : no_cmd(no_cmd), total_cmds(0), block_cmds(false), command_cb(NULL)
        {
            *no_cmd.no_cmd_resp_valid_o = 0;
            *no_cmd.no_cmd_req_ready_o = 0;
        }

        void set_nic_command_cb(NICCommandCallback cb) 
        {
            command_cb = cb;
        }

        void posedge()
        {
            handle_cmd_posedge();
            progress_completions();
        }

        void negedge()
        {
        }

        void print_stats()
        {
            printf("NIC commands: %d\n", total_cmds);
        }

        void block() {
            block_cmds = true;
        }

        void unblock() {
            block_cmds = false;
        }

        void send_completion(cmd_id_t cmd_id)
        {
            response_queue.push(cmd_id);
        }

        bool is_blocked() {
            return block_cmds;
        }

    private:
        void handle_cmd_posedge()
        {
            *no_cmd.no_cmd_req_ready_o = 0;

            if (*no_cmd.no_cmd_req_valid_i && !is_blocked())
            {
                NICCommand cmd; 
                cmd.source_addr = *no_cmd.no_cmd_req_src_addr_i;
                cmd.length = *no_cmd.no_cmd_req_length_i;
                cmd.sput_length = *no_cmd.no_cmd_req_sput_length_i;
                cmd.nid = *no_cmd.no_cmd_req_nid_i;
                cmd.fid = *no_cmd.no_cmd_req_fid_i;
                cmd.cmd_id =  *no_cmd.no_cmd_req_id_i;
                
                SIM_PRINT("NIC outbound got new command: source_addr: 0x%lx; length: %d; FID: %d (>0 is RDMA)\n", cmd.source_addr, cmd.length, cmd.fid);
                total_cmds++;

                if (command_cb) command_cb(cmd);

                *no_cmd.no_cmd_req_ready_o = 1;
            }
        }

        void progress_completions()
        {
            *no_cmd.no_cmd_resp_valid_o = 0;
            if (response_queue.empty()) return;

            cmd_id_t cmd_id = response_queue.front();
            response_queue.pop();
            *no_cmd.no_cmd_resp_valid_o = 1;
            *no_cmd.no_cmd_resp_id_o = cmd_id;
        }
    };
}