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
#include "Vpspin_verilator.h"
#include "verilated.h"
#include "SimModule.hpp"
#include "AXIMaster.hpp"
#include "pspin.hpp"
#include "spin.h"
#include "pspinsim.h"

#include <queue>
#include <vector>
#include <unordered_map>
#include <stdio.h>

#define NI_PKT_ADDR_ALIGNMENT 64

namespace PsPIN
{

    template <typename AXIPortType>
    class NICInbound : public SimModule
    {
        typedef typename AXIPortType::axi_addr_t axi_addr_t;

        typedef struct incoming_her
        {
            her_descr_t her;
            std::vector<uint8_t> pkt_data;
            size_t pkt_len;
            uint32_t wait_cycles;
        } incoming_her_t;

    public:
        ni_control_port_t &ni_ctrl;

    public:
        typedef std::function<void(uint64_t, uint64_t, uint64_t, uint64_t)> pkt_feedback_cb_t;

    private:
        AXIMaster<AXIPortType> axi_driver;
        axi_addr_t l2_pkt_buff_start;
        uint32_t l2_pkt_buff_size;
        uint32_t hers_to_send;

        //HERs that are coming from the network (virtual delay applied)
        std::queue<incoming_her_t> incoming_hers;

        //HERs that have been read and for which a DMA write is in flight
        std::queue<her_descr_t> queued_hers;

        //HERs that are ready to be sent to PsPIN (DMA completed)
        std::queue<her_descr_t> ready_hers;

        uint32_t packet_wait_cycles;

        FILE *pkt_file;
        FILE *data_file;
        uint64_t head_ptr, tail_ptr, cut_ptr;
        bool cut;
        uint32_t in_flight_packets;
        std::unordered_map<uint32_t, uint32_t> free_req_queue;

        bool her_cmd_wait;

        bool app_sent_eos;

        pkt_feedback_cb_t feedback_cb;

        //Statistics
    private:
        typedef struct pktentry
        {
            uint64_t nic_arrival_time;
            uint64_t pspin_arrival_time;
            uint32_t size;
            uint64_t user_ptr;
            uint32_t msgid;
        } pktentry_t;

        uint64_t total_bytes_sent;
        uint64_t total_pkts;

        uint64_t time_last_feedback;
        uint64_t time_first_feedback;
        uint32_t total_feedbacks;
        uint32_t ni_ctrl_stalls;

        uint64_t sum_pkt_latency;
        uint64_t min_pkt_latency;
        uint64_t max_pkt_latency;

        std::unordered_map<axi_addr_t, pktentry> pktmap;

    public:
        NICInbound<AXIPortType>(AXIPortType &ni_mst, ni_control_port_t &ni_ctrl, axi_addr_t l2_pkt_buff_start, uint32_t l2_pkt_buff_size)
            : axi_driver(ni_mst), ni_ctrl(ni_ctrl), l2_pkt_buff_start(l2_pkt_buff_start), l2_pkt_buff_size(l2_pkt_buff_size)
        {
            *ni_ctrl.her_valid_o = 0;
            *ni_ctrl.eos_o = 0;

            // Accept feedbacks
            *ni_ctrl.feedback_ready_o = 1;
            packet_wait_cycles = 0;

            pkt_file = NULL;
            data_file = NULL;

            app_sent_eos = false;

            head_ptr = 0;
            tail_ptr = 0;
            cut_ptr = 0;
            cut = false;
            in_flight_packets = 0;

            //printf("sizeof(her_descr_t): %lu\n", sizeof(her_descr_t));

            total_bytes_sent = 0;
            total_pkts = 0;
            time_last_feedback = 0;
            time_first_feedback = 0;
            total_feedbacks = 0;
            sum_pkt_latency = 0;
            min_pkt_latency = 0;
            max_pkt_latency = 0;
            ni_ctrl_stalls = 0;

            hers_to_send = 0;

            her_cmd_wait = false;
        }

        ~NICInbound()
        {
            if (data_file != NULL)
                fclose(data_file);
            if (pkt_file != NULL)
                fclose(pkt_file);
        }

        void set_feedback_cb(pkt_feedback_cb_t cb)
        {
            this->feedback_cb = cb;
        }

        void set_eos()
        {
            app_sent_eos = true;
        }

        int add_packet(her_descr_t &her, uint8_t *pkt_data, size_t pkt_len, uint32_t wait_cycles)
        {
            incoming_her_t ih;
            ih.her = her;
            ih.pkt_data.resize(pkt_len);
            memcpy(&(ih.pkt_data[0]), pkt_data, pkt_len);
            ih.pkt_len = pkt_len;
            ih.wait_cycles = wait_cycles;

            incoming_hers.push(ih);
            hers_to_send++;

            return SPIN_SUCCESS;
        }

        int read_trace(const char *pkt_filename, const char *data_filename)
        {
            // Note: this can be optimized if the packet trace becomes too big
            FILE *pkt_file = fopen(pkt_filename, "r");
            if (pkt_file == NULL)
            {
                printf("Task file not found!\n");
                return SPIN_ERR;
            }

            FILE *data_file = fopen(data_filename, "rb");
            if (data_file == NULL)
            {
                printf("Data file not found!\n");
                return SPIN_ERR;
            }

            while (!feof(pkt_file))
            {
                uint32_t msgid, hh_addr, hh_size, ph_addr, ph_size, th_addr, th_size, hmem_addr, hmem_size, pkt_size, pkt_xfer_size, eom, wait_cycles;
                int code = fscanf(pkt_file, "%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u\n", &msgid, &hh_addr, &hh_size, &ph_addr, &ph_size, &th_addr, &th_size, &hmem_addr, &hmem_size, &pkt_size, &pkt_xfer_size, &eom, &wait_cycles);
                assert(code == 13);

                uint8_t *pkt_data = new uint8_t[pkt_size];
                code = fread(&(pkt_data[0]), sizeof(uint8_t), pkt_size, data_file);
                assert(code == pkt_size);

                her_descr_t her_descr;

                // prepare handler execution request (HER)
                her_descr.mpq_meta.hh_addr = hh_addr;
                her_descr.mpq_meta.hh_size = hh_size;

                her_descr.mpq_meta.ph_addr = ph_addr;
                her_descr.mpq_meta.ph_size = ph_size;

                her_descr.mpq_meta.th_addr = th_addr;
                her_descr.mpq_meta.th_size = th_size;

                her_descr.mpq_meta.handler_mem_addr = hmem_addr;
                her_descr.mpq_meta.handler_mem_size = hmem_size;

                her_descr.mpq_meta.host_mem_addr = PCIE_START_ADDR;
                her_descr.mpq_meta.host_mem_size = 0x40000000;

                for (int i = 0; i < NUM_CLUSTERS; i++)
                {
                    her_descr.mpq_meta.scratchpad_addr[i] = 0;
                    her_descr.mpq_meta.scratchpad_size[i] = L1_SCRATCHPAD_SIZE;
                }

                her_descr.msgid = msgid;
                her_descr.her_addr = 0x0; //will be set later
                her_descr.her_size = pkt_size;
                her_descr.xfer_size = pkt_xfer_size;
                her_descr.eom = (eom == 1);

                add_packet(her_descr, pkt_data, pkt_size, wait_cycles);
            }
            fclose(data_file);
            fclose(pkt_file);

            return SPIN_SUCCESS;
        }

        bool allocate_pkt_space(uint32_t pkt_size, axi_addr_t *addr)
        {
            bool can_allocate = false;

            uint32_t segments = (pkt_size + NI_PKT_ADDR_ALIGNMENT - 1) / NI_PKT_ADDR_ALIGNMENT;
            pkt_size = segments * NI_PKT_ADDR_ALIGNMENT;

            if (tail_ptr > head_ptr || (tail_ptr == head_ptr && in_flight_packets == 0))
            {
                if (l2_pkt_buff_size - tail_ptr >= pkt_size)
                {
                    can_allocate = true;
                }
                else if (head_ptr >= pkt_size)
                {
                    cut_ptr = tail_ptr;
                    cut = true;
                    tail_ptr = 0;
                    can_allocate = true;
                }
            }
            else if (head_ptr > tail_ptr)
            {
                if (head_ptr - tail_ptr >= pkt_size)
                {
                    can_allocate = true;
                }
            }

            if (can_allocate)
            {
                *addr = l2_pkt_buff_start + tail_ptr;
                tail_ptr += pkt_size;
                in_flight_packets++;
                SIM_PRINT("NIC inbound engine: allocated %u bytes; head_ptr: %lu; tail_ptr: %lu; in_flight_packets: %lu\n", pkt_size, head_ptr, tail_ptr, in_flight_packets);
            }
            else{
                SIM_PRINT("NIC inbound engine: allocation failed! bytes: %u; head_ptr: %lu; tail_ptr: %lu; in_flight_packets: %lu\n", pkt_size, head_ptr, tail_ptr, in_flight_packets);
            }

            return can_allocate;
        }

        void free_pkt_space(axi_addr_t addr, uint32_t size)
        {
            uint32_t offset = addr - l2_pkt_buff_start;
            assert(addr >= l2_pkt_buff_start);

            uint32_t segments = (size + NI_PKT_ADDR_ALIGNMENT - 1) / NI_PKT_ADDR_ALIGNMENT;
            size = segments * NI_PKT_ADDR_ALIGNMENT;

            assert(free_req_queue.find(offset) == free_req_queue.end());
            free_req_queue[offset] = size;

            while (!free_req_queue.empty() && free_req_queue.find(head_ptr) != free_req_queue.end())
            {
                uint32_t head_ptr_increase = free_req_queue[head_ptr];
                free_req_queue.erase(head_ptr);

                head_ptr += head_ptr_increase;
                in_flight_packets--;
                SIM_PRINT("NIC inbound engine: freeing %u bytes; head_ptr: %lu; tail_ptr: %lu; in_flight_packets: %lu; cut: %u; cut_ptr: %lu\n", head_ptr_increase, head_ptr, tail_ptr, in_flight_packets, (uint32_t) cut, cut_ptr);

                if (cut && head_ptr == cut_ptr)
                {
                    head_ptr = 0;
                    cut = false;
                    SIM_PRINT("NIC inbound engine: resetting head_ptr! cut_ptr: %lu;\n", cut_ptr);
                }
            }
        }

        bool process_packet(her_descr_t &her_descr, uint8_t *pkt_data, uint32_t pkt_size)
        {
            axi_addr_t pkt_addr;
            if (!allocate_pkt_space(pkt_size, &pkt_addr))
            {
                return false;
            }

            axi_driver.write(pkt_addr, pkt_data, pkt_size, 0);

            her_descr.her_addr = pkt_addr;
            her_descr.nic_arrival_time = sim_time();

            queued_hers.push(her_descr);

            return true;
        }

        void progress_incoming_packets()
        {
            if (incoming_hers.empty())
                return;

            if (packet_wait_cycles > 0)
            {
                packet_wait_cycles--;
                if (packet_wait_cycles > 0)
                    return;
            }

            incoming_her_t &ih = incoming_hers.front();

            if (process_packet(ih.her, &(ih.pkt_data[0]), ih.pkt_len))
            {
                // we won't serve the next packet before wait_cycles;
                packet_wait_cycles = ih.wait_cycles;

                incoming_hers.pop();
            }
            else
            {
                //the packet is here and we cannot push it to PsPIN because of no space in L2;
                //still spending "wait" cycles.
                ih.wait_cycles = (ih.wait_cycles > 0) ? ih.wait_cycles-- : 0;
            }
        }

        void posedge()
        {
            if (*ni_ctrl.pspin_active_i)
            {
                progress_axi_writes();
                axi_driver.posedge();
                progress_axi_write_responses();
                progress_incoming_packets();
                her_progress_posedge();
                feedback_progress();
            }
        }

        void negedge()
        {
            axi_driver.negedge();
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

            her_descr_t her = ready_hers.front();

            *ni_ctrl.her_o.msgid = her.msgid;
            *ni_ctrl.her_o.eom = her.eom;
            *ni_ctrl.her_o.her_addr = her.her_addr;
            *ni_ctrl.her_o.her_size = her.her_size;
            *ni_ctrl.her_o.xfer_size = her.xfer_size;
            *ni_ctrl.her_o.mpq_meta.handler_mem_addr = her.mpq_meta.handler_mem_addr;
            *ni_ctrl.her_o.mpq_meta.handler_mem_size = her.mpq_meta.handler_mem_size;
            *ni_ctrl.her_o.mpq_meta.host_mem_addr = her.mpq_meta.host_mem_addr;
            *ni_ctrl.her_o.mpq_meta.host_mem_size = her.mpq_meta.host_mem_size;
            *ni_ctrl.her_o.mpq_meta.hh_addr = her.mpq_meta.hh_addr;
            *ni_ctrl.her_o.mpq_meta.hh_size = her.mpq_meta.hh_size;
            *ni_ctrl.her_o.mpq_meta.ph_addr = her.mpq_meta.ph_addr;
            *ni_ctrl.her_o.mpq_meta.ph_size = her.mpq_meta.ph_size;
            *ni_ctrl.her_o.mpq_meta.th_addr = her.mpq_meta.th_addr;
            *ni_ctrl.her_o.mpq_meta.th_size = her.mpq_meta.th_size;
            *ni_ctrl.her_o.mpq_meta.scratchpad_addr[0] = her.mpq_meta.scratchpad_addr[0];
            *ni_ctrl.her_o.mpq_meta.scratchpad_addr[1] = her.mpq_meta.scratchpad_addr[1];
            *ni_ctrl.her_o.mpq_meta.scratchpad_addr[2] = her.mpq_meta.scratchpad_addr[2];
            *ni_ctrl.her_o.mpq_meta.scratchpad_addr[3] = her.mpq_meta.scratchpad_addr[3];
            *ni_ctrl.her_o.mpq_meta.scratchpad_size[0] = her.mpq_meta.scratchpad_size[0];
            *ni_ctrl.her_o.mpq_meta.scratchpad_size[1] = her.mpq_meta.scratchpad_size[1];
            *ni_ctrl.her_o.mpq_meta.scratchpad_size[2] = her.mpq_meta.scratchpad_size[2];
            *ni_ctrl.her_o.mpq_meta.scratchpad_size[3] = her.mpq_meta.scratchpad_size[3];

            *ni_ctrl.her_valid_o = 1;

            hers_to_send--;

            ready_hers.pop();

            SIM_PRINT("HER sent (0x%x)\n", *ni_ctrl.her_o.her_addr);

            pktentry_t pktentry;
            pktentry.pspin_arrival_time = sim_time();
            pktentry.nic_arrival_time = her.nic_arrival_time;
            pktentry.size = her.her_size;
            pktentry.user_ptr = her.user_ptr;
            pktentry.msgid = her.msgid;

            assert(pktmap.find(*ni_ctrl.her_o.her_addr) == pktmap.end());
            pktmap[*ni_ctrl.her_o.her_addr] = pktentry;

            //stats
            total_bytes_sent += her.her_size;
            total_pkts++;

            if (hers_to_send == 0 && app_sent_eos)
            {
                *ni_ctrl.eos_o = 1;
            }
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
                pktentry_t pktentry = pktmap[*ni_ctrl.feedback_her_addr_i];
                uint64_t latency = (uint64_t)(sim_time() - pktentry.nic_arrival_time);

                SIM_PRINT("INFO FEEDBACK 0x%x %lu %u %u\n", *ni_ctrl.feedback_her_addr_i, latency, pktentry.size, pktentry.msgid);

                assert(*ni_ctrl.feedback_her_size_i == pktentry.size);
                free_pkt_space(*ni_ctrl.feedback_her_addr_i, *ni_ctrl.feedback_her_size_i);

                sum_pkt_latency += latency;

                if (feedback_cb)
                    feedback_cb(pktentry.user_ptr, pktentry.nic_arrival_time, pktentry.pspin_arrival_time, sim_time());

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

        void progress_axi_writes()
        {
            if (axi_driver.has_aw_beat() && axi_driver.can_send_aw_beat())
            {
                axi_driver.send_aw_beat();
            }

            if (axi_driver.has_w_beat() && axi_driver.can_send_w_beat())
            {
                axi_driver.send_w_beat();
            }
        }

        void progress_axi_write_responses()
        {
            if (!axi_driver.has_b_beat())
                return;

            bool write_completed = axi_driver.consume_b_beat();

            if (write_completed)
            {
                assert(!queued_hers.empty());
                her_descr_t her = queued_hers.front();
                queued_hers.pop();
                ready_hers.push(her);
            }
        }

    public:
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
    };

} // namespace PsPIN
