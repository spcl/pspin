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
    class NIMaster: public SimModule
    {
    public:
        typedef std::function<void(void)> HERCompletetionCallback;

    private:

        typedef struct her_entry 
        {
            her_descr_t* descr;
            HERCompletetionCallback cb;
            uint64_t nic_arrival_time;
            uint64_t pspin_arrival_time;
        } her_entry_t;

    private:
        uint32_t her_buffer_size;
        std::queue<her_entry_t> ready_hers;
        std::unordered_map<mem_addr_t, her_entry_t> pktmap;
        ni_control_port_t &ni_ctrl;
        bool her_cmd_wait;
        uint32_t ni_ctrl_stalls;
        uint64_t total_bytes_sent;
        uint64_t total_pkts;
        uint64_t sum_pkt_latency;
        uint64_t min_pkt_latency;
        uint64_t max_pkt_latency;
        uint64_t time_last_feedback;
        uint64_t time_first_feedback;
        uint32_t total_feedbacks;

    public: 

        NIMaster(ni_control_port_t &ni_ctrl, uint32_t her_buffer_size = 32) 
        : her_buffer_size(her_buffer_size), 
          ni_ctrl(ni_ctrl),
          her_cmd_wait(false), 
          ni_ctrl_stalls(0),
          total_bytes_sent(0),
          total_pkts(0),
          sum_pkt_latency(0),
          min_pkt_latency(0),
          max_pkt_latency(0),
          time_last_feedback(0),
          time_first_feedback(0),
          total_feedbacks(0)
        {
            
            *ni_ctrl.her_valid_o = 0;
            *ni_ctrl.eos_o = 0;

            // Accept feedbacks
            *ni_ctrl.feedback_ready_o = 1;
        }

        void set_her_buffer_size(uint32_t size) 
        {
            her_buffer_size = size;
        }

        int send_her(her_descr_t *her, HERCompletetionCallback cb) {
            if (!can_send_her()) return -1;
            her_entry_t entry;
            entry.descr = her;
            entry.cb = cb;
            entry.nic_arrival_time = sim_time();
            ready_hers.push(entry);
            return 0;
        } 

        bool can_send_her() {
            return ready_hers.size() < her_buffer_size;
        }

        void shutdown() {
            *ni_ctrl.eos_o = 1;
        }

        void print_stats()
        {
            double avg_pkt_length = ((double)total_bytes_sent) / total_pkts;
            double avg_intra_feedback = ((double)(time_last_feedback - time_first_feedback)) / (1000 * (total_feedbacks - 1));
            double avg_feedback_throughput = THROUGHPUT_1GHZ(avg_intra_feedback, avg_pkt_length);
            double avg_pkt_latency = ((double)sum_pkt_latency) / (1000 * total_pkts);

            printf("NIC inbound engine:\n");
            printf("\tPackets: %lu; Bytes: %lu\n", total_pkts, total_bytes_sent);
            printf("\tAvg packet length: %.3lf B\n", avg_pkt_length);
            printf("\tFeedback throughput: %.3lf Gbit/s (feedback arrival time: %.3lf ns)\n", avg_feedback_throughput, avg_intra_feedback);
            printf("\tPacket latency: avg: %.3lf ns; min: %lu ns; max: %lu ns\n", avg_pkt_latency, min_pkt_latency / 1000, max_pkt_latency / 1000);
            printf("\tHER stalls: %d\n", ni_ctrl_stalls);
        }

        void posedge()
        {
            if (*ni_ctrl.pspin_active_i)
            {
                her_progress_posedge();
                feedback_progress();
            }
        }

        void negedge()
        {
            her_progress_negedge();
        }


    private:
        // Progress HERs
        void her_progress_posedge()
        {
            if (her_cmd_wait)
            {
                ni_ctrl_stalls++;
                return;
            }

            *ni_ctrl.her_valid_o = 0;

            if (ready_hers.empty())
            {
                return;
            }

            her_entry_t &her_entry = ready_hers.front();
            her_descr_t *her = her_entry.descr;

            *ni_ctrl.her_o.msgid = her->msgid;
            *ni_ctrl.her_o.home_cluster_id = her->home_cluster_id;
            *ni_ctrl.her_o.eom = her->eom;
            *ni_ctrl.her_o.her_addr = her->her_addr;
            *ni_ctrl.her_o.her_size = her->her_size;
            *ni_ctrl.her_o.xfer_size = her->xfer_size;
            *ni_ctrl.her_o.mpq_meta.handler_mem_addr = her->mpq_meta.handler_mem_addr;
            *ni_ctrl.her_o.mpq_meta.handler_mem_size = her->mpq_meta.handler_mem_size;
            *ni_ctrl.her_o.mpq_meta.host_mem_addr = her->mpq_meta.host_mem_addr;
            *ni_ctrl.her_o.mpq_meta.host_mem_size = her->mpq_meta.host_mem_size;
            *ni_ctrl.her_o.mpq_meta.hh_addr = her->mpq_meta.hh_addr;
            *ni_ctrl.her_o.mpq_meta.hh_size = her->mpq_meta.hh_size;
            *ni_ctrl.her_o.mpq_meta.ph_addr = her->mpq_meta.ph_addr;
            *ni_ctrl.her_o.mpq_meta.ph_size = her->mpq_meta.ph_size;
            *ni_ctrl.her_o.mpq_meta.th_addr = her->mpq_meta.th_addr;
            *ni_ctrl.her_o.mpq_meta.th_size = her->mpq_meta.th_size;
            *ni_ctrl.her_o.mpq_meta.scratchpad_addr[0] = her->mpq_meta.scratchpad_addr[0];
            *ni_ctrl.her_o.mpq_meta.scratchpad_addr[1] = her->mpq_meta.scratchpad_addr[1];
            *ni_ctrl.her_o.mpq_meta.scratchpad_addr[2] = her->mpq_meta.scratchpad_addr[2];
            *ni_ctrl.her_o.mpq_meta.scratchpad_addr[3] = her->mpq_meta.scratchpad_addr[3];
            *ni_ctrl.her_o.mpq_meta.scratchpad_size[0] = her->mpq_meta.scratchpad_size[0];
            *ni_ctrl.her_o.mpq_meta.scratchpad_size[1] = her->mpq_meta.scratchpad_size[1];
            *ni_ctrl.her_o.mpq_meta.scratchpad_size[2] = her->mpq_meta.scratchpad_size[2];
            *ni_ctrl.her_o.mpq_meta.scratchpad_size[3] = her->mpq_meta.scratchpad_size[3];

            *ni_ctrl.her_valid_o = 1;

            SIM_PRINT("HER sent (0x%x)\n", *ni_ctrl.her_o.her_addr);

            her_entry.pspin_arrival_time = sim_time();
  
            assert(pktmap.find(*ni_ctrl.her_o.her_addr) == pktmap.end());
            pktmap[*ni_ctrl.her_o.her_addr] = her_entry;

            ready_hers.pop();

            //stats
            total_bytes_sent += her->her_size;
            total_pkts++;
        }

        void her_progress_negedge()
        {
            her_cmd_wait = false;
            if (*ni_ctrl.her_valid_o && !(*ni_ctrl.her_ready_i))
            {
                her_cmd_wait = true;
            }
        }

        // Get feedback
        void feedback_progress()
        {
            if (*ni_ctrl.feedback_ready_o && *ni_ctrl.feedback_valid_i)
            {
                assert(pktmap.find(*ni_ctrl.feedback_her_addr_i) != pktmap.end());
                her_entry_t pktentry = pktmap[*ni_ctrl.feedback_her_addr_i];
                uint64_t latency = (uint64_t)(sim_time() - pktentry.nic_arrival_time);

                SIM_PRINT("INFO FEEDBACK 0x%x %lu %u\n", *ni_ctrl.feedback_her_addr_i, latency, pktentry.descr->her_size);

                assert(*ni_ctrl.feedback_her_size_i == pktentry.descr->her_size);

                sum_pkt_latency += latency;

                if (pktentry.cb) {
                    pktentry.cb();
                }

                pktmap.erase(*ni_ctrl.feedback_her_addr_i);

                if (total_feedbacks == 0)
                {
                    time_first_feedback = sim_time();
                    min_pkt_latency = latency;
                    max_pkt_latency = latency;
                }
                else
                {
                    min_pkt_latency = std::min(min_pkt_latency, latency);
                    max_pkt_latency = std::max(max_pkt_latency, latency);
                }

                time_last_feedback = sim_time();

                total_feedbacks++;
            }
        }
    };
}