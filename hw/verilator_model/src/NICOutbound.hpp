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

#include <queue>
#include <stdio.h>

#define RDMA_HEADER_LENGTH 32
#define NUM_PARALLEL_CMD 16

// The network delay is computed by slicing the packet in words
// and applying G to the number of segments. This is to
#define WORD_SIZE 64 

namespace PsPIN
{
    template <typename AXIPortType>
    class NICOutbound : public SimModule
    {

    private:
        class NetworkPacket
        {
        public:
            uint64_t source_addr;
            uint32_t current_offset;
            uint32_t length;
            uint32_t payload_length;
            uint8_t cmd_id;
            bool is_last;
            std::vector<uint8_t> data;

            NetworkPacket(uint32_t length) : length(length)
            {
                current_offset = 0;
                data.resize(length);
            }
        };

        class NICCommand 
        {
            public:
                uint64_t source_addr;
                uint32_t length;
                uint32_t nid;
                uint32_t fid;
                uint8_t cmd_id;
        };

        class Packetizer
        {
            private: 
                uint32_t num_parallel_cmds;
                uint32_t max_packet_len;
                std::queue<NICCommand> commands;

            public:
                Packetizer(uint32_t num_parallel_cmds, uint32_t max_packet_len) : num_parallel_cmds(num_parallel_cmds), max_packet_len(max_packet_len)
                {
                    ;
                }

                bool has_free_cmd_slot()
                {
                    return commands.size() < num_parallel_cmds;
                }

                bool has_packets()
                {
                    return commands.size() > 0;
                }

                void new_cmd(NICCommand cmd)
                {
                    assert(commands.size() < num_parallel_cmds);
                    commands.push(cmd);
                }

                NetworkPacket get_next_packet()
                {
                    assert(!commands.empty());
                    NICCommand cmd = commands.front();
                    commands.pop();

                    uint32_t header_length = 0;
                    if (cmd.fid>0) { /* RDMA (can be multi packet) */
                        header_length = RDMA_HEADER_LENGTH;
                    } else { /* single packet */
                        assert(cmd.length <= max_packet_len);
                    }

                    uint32_t payloadlen = std::min(max_packet_len - header_length, cmd.length);
                    uint32_t pktlen = header_length + payloadlen;

                    NetworkPacket pkt(pktlen);

                    pkt.cmd_id = cmd.cmd_id;
                    pkt.is_last = cmd.length - payloadlen == 0;
                    pkt.length = pktlen;
                    pkt.payload_length = payloadlen;
                    pkt.source_addr = cmd.source_addr;

                    cmd.length -= payloadlen;
                    cmd.source_addr += payloadlen;

                    //printf("generating packet: length: %d; payload: %d; new cmd length: %d; next pkt addr: 0x%lx\n", pktlen, payloadlen, cmd.length, cmd.source_addr);

                    if (cmd.length>0){
                        commands.push(cmd);
                    }

                    return pkt;
                }
        };

    public:
            typedef std::function<void(uint8_t*, size_t)> out_packet_cb_t;

    private:
        AXIMaster<AXIPortType> axi_driver;
        no_cmd_port &no_cmd;
        double network_G; //ns
        uint32_t max_pkt_length;
        uint32_t network_buffer_size;

        uint32_t wait_cycles;

        std::queue<NetworkPacket> network_queue;

        std::queue<NetworkPacket> dma_pkt_in_flight;

        Packetizer packetizer;

    public:
        out_packet_cb_t pktout_cb;

    //statistics
    private:
        uint32_t total_cmds;
        uint32_t total_pkts;
        uint32_t total_bytes;
        uint64_t time_first_pkt;
        uint64_t time_last_pkt;

    public:
        NICOutbound<AXIPortType>(AXIPortType &no_mst, no_cmd_port_t &no_cmd, double network_G, uint32_t max_pkt_length, uint32_t network_buffer_size)
            : axi_driver(no_mst), no_cmd(no_cmd), network_G(network_G), max_pkt_length(max_pkt_length), network_buffer_size(network_buffer_size), packetizer(NUM_PARALLEL_CMD, max_pkt_length)
        {
            *no_cmd.no_cmd_resp_valid_o = 0;
            *no_cmd.no_cmd_req_ready_o = 0;

            wait_cycles = 0;

            total_cmds = 0;
            total_pkts = 0;
            total_bytes = 0;
            time_first_pkt = 0;
            time_last_pkt = 0;
        }

        void posedge()
        {
            progress_axi_reads();
            axi_driver.posedge();
            progress_axi_read_responses();
            progress_netqueue();
            handle_cmd_posedge();
            progress_packets();
        }

        void negedge()
        {
            axi_driver.negedge();
        }

        void set_packet_out_cb(out_packet_cb_t cb)
        {
            this->pktout_cb = cb;
        }

    private:
        void handle_cmd_posedge()
        {
            *no_cmd.no_cmd_req_ready_o = 0;

            bool can_accept_cmd = packetizer.has_free_cmd_slot();

            if (*no_cmd.no_cmd_req_valid_i && can_accept_cmd)
            {

                NICCommand cmd; 
                cmd.source_addr = *no_cmd.no_cmd_req_src_addr_i;
                cmd.length = *no_cmd.no_cmd_req_length_i;
                cmd.nid = *no_cmd.no_cmd_req_nid_i;
                cmd.fid = *no_cmd.no_cmd_req_fid_i;
                cmd.cmd_id =  *no_cmd.no_cmd_req_id_i;
                
                assert(cmd.fid>0 || cmd.length <= max_pkt_length);

                SIM_PRINT("NIC outbound got new command: source_addr: 0x%lx; length: %d; FID: %d (>0 is RDMA)\n", cmd.source_addr, cmd.length, cmd.fid);
                total_cmds++;

                packetizer.new_cmd(cmd);

                *no_cmd.no_cmd_req_ready_o = 1;
            }
        }

        void progress_packets()
        {
            bool can_send_pkt = network_queue.size() + dma_pkt_in_flight.size() < network_buffer_size;
            if (packetizer.has_packets() && can_send_pkt)
            {
                NetworkPacket pkt = packetizer.get_next_packet();
                axi_driver.read(pkt.source_addr, pkt.payload_length);
                dma_pkt_in_flight.push(pkt);
            }
        }

        void progress_netqueue()
        {
            *no_cmd.no_cmd_resp_valid_o = 0;

            if (wait_cycles > 0)
            {
                wait_cycles--;
                if (wait_cycles > 0) return;
            }

            if (!network_queue.empty())
            {
                NetworkPacket &pkt = network_queue.front();
                
                wait_cycles = ((uint32_t)(network_G * WORD_SIZE)) * std::floor((double) pkt.length / WORD_SIZE);

                if (pkt.is_last)
                {
                    *no_cmd.no_cmd_resp_valid_o = 1;
                    *no_cmd.no_cmd_resp_id_o = pkt.cmd_id;
                }

                // TODO: packet is ready. This is the point where we can do something with it.

                if (pktout_cb) pktout_cb((uint8_t*) &(pkt.data[0]), pkt.length);

                SIM_PRINT("packet sent; size: %d; wait_cycles: %d (G: %lf); is_last: %d\n", pkt.length, wait_cycles, network_G, (uint32_t) pkt.is_last);

                if (total_pkts==0) time_first_pkt = sim_time();
                time_last_pkt = sim_time();
                total_pkts++;
                total_bytes += pkt.length;

                network_queue.pop();

            }
        }

        void progress_axi_reads()
        {
            if (axi_driver.has_ar_beat() && axi_driver.can_send_ar_beat())
            {
                axi_driver.send_ar_beat();
            }
        }

        void progress_axi_read_responses()
        {

            if (axi_driver.has_r_beat())
            {
                bool read_complete;
                uint32_t length = AXI_SW;

                assert(!dma_pkt_in_flight.empty());
                NetworkPacket &pkt = dma_pkt_in_flight.front();

                uint8_t *dest_ptr = ((uint8_t *)&(pkt.data[0])) + pkt.current_offset;
                read_complete = axi_driver.consume_r_beat(dest_ptr, length);

                pkt.current_offset += length;

                if (read_complete)
                {
                    //printf("pkt.current_offset: %d; pkt.length: %d\n", pkt.current_offset, pkt.length);
                    assert(pkt.current_offset == pkt.payload_length);
                    network_queue.push(pkt);
                    dma_pkt_in_flight.pop();
                }
            }
        }

        public:
            void print_stats()
            {
                double avg_pkt_length = ((double) total_bytes) / total_pkts;            
                double avg_intra_pkt = ((double) (time_last_pkt - time_first_pkt)) / (1000*(total_pkts-1));
                double avg_pkt_throughput = THROUGHPUT_1GHZ(avg_intra_pkt, avg_pkt_length);            

                printf("NIC outbound engine:\n");
                printf("\tCommands: %d; Packets: %d; Bytes: %d\n", total_cmds, total_pkts, total_bytes);
                printf("\tAvg packet length: %.3lf B\n", avg_pkt_length);
                printf("\tPacket throughput: %.3lf Gbit/s (pkt departure time: %.3lf ns)\n", avg_pkt_throughput, avg_intra_pkt);
            }
    };

} // namespace PsPIN