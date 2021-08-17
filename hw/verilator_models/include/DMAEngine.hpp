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

#define DEFAULT_BUFF_SIZE 32

namespace PsPIN
{
    using std::placeholders::_1;

    /** 
     * Simple DMAEngine that takes a memcpy like interface as commands. 
     */
    template <typename AXIPortType>
    class DMAEngine : public SimModule
    {

    public:
        typedef std::function<void(void)> mst_write_cb_t;
        typedef std::function<void(void)> mst_read_cb_t;

    private:
        typedef struct write_descr
        {
            mst_write_cb_t cb;
        } write_descr_t;

        typedef struct read_descr
        {
            uint8_t *data;
            uint32_t offset;
            size_t len;
            mst_read_cb_t cb;
        } read_descr_t;

    private:
        AXIMaster<AXIPortType> axi_driver;
        std::queue<read_descr_t> in_flight_reads;
        std::queue<write_descr_t> in_flight_writes;

        uint32_t bytes_written, bytes_read;
        uint32_t write_buff_size;
        uint32_t read_buff_size;

    public:
        DMAEngine<AXIPortType>(AXIPortType &axi_mst) 
        : axi_driver(axi_mst)
        {
            bytes_written = 0;
            bytes_read = 0;
            write_buff_size = DEFAULT_BUFF_SIZE;
            read_buff_size = DEFAULT_BUFF_SIZE;
        }

        bool can_write() {
            return in_flight_writes.size() < write_buff_size;
        }

        bool can_read() {
            return in_flight_reads.size() < read_buff_size;
        }

        void set_write_buff_size(uint32_t size)
        {
            write_buff_size = size;
        }

        void set_read_buff_size(uint32_t size) 
        {
            read_buff_size = size;
        }

        void write(uint32_t nic_mem_addr, uint8_t *data, size_t len, mst_write_cb_t cb)
        {
            assert(can_write());
            write_descr_t write;
            write.cb = cb;
            axi_driver.write(nic_mem_addr, data, len, 0);
            in_flight_writes.push(write);

            bytes_written += len;
        }

        void read(uint32_t nic_mem_addr, uint8_t *data, size_t len, mst_read_cb_t cb)
        {
            assert(can_read());
            read_descr_t read;
            read.data = data;
            read.offset = 0;
            read.len = len;
            read.cb = cb;
            axi_driver.read(nic_mem_addr, len);
            in_flight_reads.push(read);

            bytes_read += len;
        }

    private:
        void posedge()
        {
            progress_axi_writes();
            progress_axi_reads();
            axi_driver.posedge();
            progress_axi_write_responses();
            progress_axi_read_responses();        
        }

        void negedge()
        {
            axi_driver.negedge();
        }

        void print_stats()
        {
            printf("PCIe Master:\n");
            printf("\tBytes written: %d; Bytes read: %d\n", bytes_written, bytes_read);
        
        }

    private:
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
                assert(!in_flight_writes.empty());
                write_descr_t &write_descr = in_flight_writes.front();
                if (write_descr.cb) write_descr.cb();
                in_flight_writes.pop();
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

                assert(!in_flight_reads.empty());
                read_descr_t &read_descr = in_flight_reads.front();
                assert(read_descr.offset + length <= read_descr.len);
                uint8_t *dest_ptr = read_descr.data + read_descr.offset;
                read_descr.offset += length;

                //do something with this data
                read_complete = axi_driver.consume_r_beat(dest_ptr, length);

                if (read_complete)
                {
                    // read complete
                    assert(read_descr.offset == read_descr.len);
                    if (read_descr.cb) read_descr.cb();
                    in_flight_reads.pop();
                }
            }
        }
    };

} // namespace PsPIN