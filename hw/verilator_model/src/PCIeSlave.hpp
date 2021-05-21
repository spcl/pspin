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
#include "AXISlave.hpp"
#include "pspin.hpp"

#include <queue>
#include <stdio.h>

namespace PsPIN
{
    using std::placeholders::_1;

    template <typename AXISlvPortType>
    class PCIeSlave : public SimModule
    {
    
        typedef typename AXISlave<AXISlvPortType>::w_beat_request_t w_beat_request_t;
        typedef typename AXISlave<AXISlvPortType>::r_beat_request_t r_beat_request_t;

    private:
        typedef struct pcie_write 
        {
            w_beat_request_t req;
            uint64_t time;
        } pcie_write_t;

        typedef struct pcie_read
        {
            r_beat_request_t req;
            uint64_t time;
        } pcie_read_t;

    private:
        AXISlave<AXISlvPortType> axi_driver_slv;

        uint32_t pcie_L;
        double pcie_G;

        uint32_t write_wait_cycles;
        uint32_t read_wait_cycles;

        std::queue<pcie_write_t> in_flight_write_requests;
        std::queue<pcie_read_t> in_flight_read_requests;

    public:
        typedef std::function<void(uint64_t, uint8_t*, size_t)> slv_write_cb_t;
        typedef std::function<void(uint64_t, uint8_t*, size_t)> slv_read_cb_t;

    // Statistics
    private:
        uint32_t bytes_written;
        uint32_t bytes_read;
        uint64_t time_first_read;
        uint64_t time_last_write;
        uint64_t time_first_write;
        uint64_t time_last_read;
        uint32_t num_reads;
        uint32_t num_writes;

        slv_write_cb_t slv_write_cb;
        slv_read_cb_t slv_read_cb;

    public:
        PCIeSlave(AXISlvPortType &axi_slv, uint32_t aw_buffer_size, uint32_t w_buffer_size, uint32_t ar_buffer_size, uint32_t r_buffer_size, uint32_t b_buffer_size, uint32_t pcie_L, double pcie_G)
        : axi_driver_slv(axi_slv), pcie_L(pcie_L), pcie_G(pcie_G)
        {
            write_wait_cycles = 0;
            read_wait_cycles = 0;

            axi_driver_slv.set_ar_buffer(ar_buffer_size);
            axi_driver_slv.set_aw_buffer(aw_buffer_size);
            axi_driver_slv.set_w_buffer(w_buffer_size);
            axi_driver_slv.set_r_buffer(r_buffer_size);
            axi_driver_slv.set_b_buffer(b_buffer_size);

            bytes_written = 0;
            bytes_read = 0;
            time_first_read = 0;
            time_last_write = 0;
            time_first_write = 0;
            time_last_read = 0;
            num_reads = 0;
            num_writes = 0;
        }

        void set_slv_write_cb(slv_write_cb_t cb)
        {
            this->slv_write_cb = cb;
        }

        void set_slv_read_cb(slv_read_cb_t cb)
        {
            this->slv_read_cb = cb;
        }

    private: 

        void progress_new_writes() 
        {
            if (write_wait_cycles > 0) {
                write_wait_cycles--;
                if (write_wait_cycles > 0) return;
            }

            if (axi_driver_slv.has_w_beat()) 
            {
                w_beat_request_t w_beat_req = axi_driver_slv.get_next_w_beat();

                pcie_write_t write;
                write.req = w_beat_req;
                write.time = sim_time() + pcie_L;

                in_flight_write_requests.push(write);

                write_wait_cycles = (uint32_t) (pcie_G * w_beat_req.data_size);
                //SIM_PRINT("PCIe write wait cycles: %u\n", write_wait_cycles);
            }
        }


        void progress_in_flight_writes()
        {
            if (in_flight_write_requests.empty()) return;

            pcie_write_t &write = in_flight_write_requests.front();

            if (sim_time() >= write.time && axi_driver_slv.can_send_b_beat())
            {
                // TODO: consume data here!
                assert(write.req.w_beat.w_strb>0);
                //int fs = __builtin_clzl(write.req.w_beat.w_strb);
                int fs = __builtin_ffsl(write.req.w_beat.w_strb) - 1;

                //SIM_PRINT("PCIe got data: addr: %lx; offset: %d; actual address: %lx; size: %d (last: %u)!\n", write.req.addr, fs, write.req.addr + fs, write.req.data_size, (uint32_t) write.req.w_beat.w_last);
                //for (int i=0; i<16; i++){ printf("%x ", ((uint32_t *) (write.req.w_beat.w_data))[i]); }
                //uint64_t data = ((uint64_t *) write.req.w_beat.w_data)[0];
                //printf("\n U64: %lx\n", data);

                if (slv_write_cb) slv_write_cb(write.req.addr + fs, write.req.w_beat.w_data + fs, write.req.data_size);

                bytes_written += write.req.data_size;
                if (num_writes==0) time_first_write = sim_time();
                num_writes++;
                time_last_write = sim_time();

                if (write.req.w_beat.w_last) 
                {
                    axi_driver_slv.send_b_beat();
                }

                in_flight_write_requests.pop();
            }
        }


        void progress_new_reads()
        {
           if (read_wait_cycles > 0) {
                read_wait_cycles--;
                return;
            }

            if (axi_driver_slv.has_r_beat()) 
            {
                r_beat_request_t r_beat_req = axi_driver_slv.get_next_r_beat();

                pcie_read_t read;
                read.req = r_beat_req;
                read.time = sim_time() + pcie_L;

                in_flight_read_requests.push(read);
                
                read_wait_cycles = (uint32_t) (pcie_G * r_beat_req.data_size);
            }
        }


        void progress_in_flight_reads()
        {
            if (in_flight_read_requests.empty()) return;

            pcie_read_t &read = in_flight_read_requests.front();

            if (sim_time() >= read.time && axi_driver_slv.can_send_r_beat())
            {
                // TODO: copy data here (memcpy in read.req.r_beat.r_data)!
                SIM_PRINT("PCIe: got read request (data size: %d)!\n", read.req.data_size);
                if (slv_read_cb) slv_read_cb(read.req.addr, read.req.r_beat.r_data, read.req.data_size);

                bytes_read += read.req.data_size;
                if (num_reads==0) time_first_read = sim_time();
                num_reads++;
                time_last_read = sim_time();

                axi_driver_slv.send_r_beat(read.req.r_beat);
                in_flight_read_requests.pop();
            }
        }


    private:

        void posedge()
        {
            //push staff on the AXI interface
            progress_in_flight_reads();
            progress_in_flight_writes();

            //progress AXI interface
            //axi_driver_mst.posedge();
            axi_driver_slv.posedge();

            //sample signals from AXI interface
            progress_new_reads();
            progress_new_writes();
        }

        void negedge()
        {
            //axi_driver_mst.negedge();
            axi_driver_slv.negedge();
        }

    public: 
        void print_stats()
        {
            double write_time = ((double) (time_last_write - time_first_write)) / 1000;
            double read_time = ((double) (time_last_read - time_first_read)) / 1000;
            double write_throghput = THROUGHPUT_1GHZ(write_time, bytes_written);            
            double read_throghput = THROUGHPUT_1GHZ(read_time, bytes_read);            

            printf("PCIe Slave:\n");
            printf("\tWrites: beats: %d; bytes: %d; avg throughput: %.03lf Gbit/s\n", num_writes, bytes_written, write_throghput);
            printf("\tReads: beats: %d; bytes: %d; avg throughput: %.03lf Gbit/s\n", num_reads, bytes_read, read_throghput);
        }
    };

} // namespace PsPIN
