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

#include "AXIDriver.hpp"

namespace PsPIN
{

    template <typename AXIPortType>
    class AXISlave : public AXIDriver<AXIPortType>
    {
        using typename AXIDriver<AXIPortType>::axi_ax_beat_t;
        using typename AXIDriver<AXIPortType>::axi_b_beat_t;
        using typename AXIDriver<AXIPortType>::axi_r_beat_t;
        using typename AXIDriver<AXIPortType>::axi_w_beat_t;

        using AXIDriver<AXIPortType>::port;
        using AXIDriver<AXIPortType>::create_ax_beats;
        using AXIDriver<AXIPortType>::beat_lower_byte;
        using AXIDriver<AXIPortType>::beat_upper_byte;

        typedef typename AXIPortType::axi_addr_t axi_addr_t;

    public:
        typedef struct r_beat_request
        {
            axi_addr_t addr;
            uint32_t data_size;
            axi_r_beat_t r_beat;
        } r_beat_request_t;

        typedef struct w_beat_request
        {
            axi_addr_t addr;
            uint32_t data_size;
            axi_w_beat_t w_beat;
        } w_beat_request_t;

    private:
        uint32_t aw_beats_buffer_size;
        uint32_t ar_beats_buffer_size;
        uint32_t w_beats_buffer_size;
        uint32_t r_beats_buffer_size;
        uint32_t b_beats_buffer_size;

        std::queue<axi_ax_beat_t> aw_beats;
        std::queue<axi_ax_beat_t> ar_beats;
        std::queue<axi_b_beat_t> b_beats;
        std::queue<axi_r_beat_t> r_beats;

        std::queue<axi_ax_beat_t> aw_pending_resp;
        std::queue<w_beat_request_t> w_beat_requests;

    private:
        bool r_wait;
        bool b_wait;

    public:
        AXISlave(AXIPortType &port)
            : AXIDriver<AXIPortType>(port)
        {
            r_wait = 0;
            b_wait = 0;

            *port.ar_ready = 0;
            *port.aw_ready = 0;
            *port.w_ready = 0;
            *port.r_valid = 0;
            *port.b_valid = 0;

            aw_beats_buffer_size = 0;
            ar_beats_buffer_size = 0;
            w_beats_buffer_size = 0;
            r_beats_buffer_size = 0;
            b_beats_buffer_size = 0;
        }

        void set_aw_buffer(uint32_t aw_buffer_size)
        {
            aw_beats_buffer_size = aw_buffer_size;
        }

        void set_ar_buffer(uint32_t ar_buffer_size)
        {
            ar_beats_buffer_size = ar_buffer_size;
        }

        void set_w_buffer(uint32_t w_buffer_size)
        {
            w_beats_buffer_size = w_buffer_size;
        }

        void set_r_buffer(uint32_t r_buffer_size)
        {
            r_beats_buffer_size = r_buffer_size;
        }

        void set_b_buffer(uint32_t b_buffer_size)
        {
            b_beats_buffer_size = b_buffer_size;
        }

        void posedge()
        {
            aw_posedge();
            ar_posedge();
            w_posedge();
            r_posedge();
            b_posedge();
        }

        void negedge()
        {
            aw_negedge();
            ar_negedge();
            w_negedge();
            r_negedge();
            b_negedge();
        }

        bool can_send_r_beat()
        {
            return r_beats_buffer_size == 0 || r_beats.size() < r_beats_buffer_size;
        }

        void send_r_beat(axi_r_beat_t beat)
        {
            assert(can_send_r_beat());
            r_beats.push(beat);
        }

        bool can_send_b_beat()
        {
            return b_beats_buffer_size == 0 || b_beats.size() < b_beats_buffer_size;
        }

        void send_b_beat()
        {
            assert(!aw_pending_resp.empty());
            assert(can_send_b_beat());
            axi_ax_beat_t &aw = aw_pending_resp.front();

            // prepare B beat
            axi_b_beat_t b;
            b.b_resp = AXI_RESP_OKAY;
            b.b_id = aw.ax_id;
            b.b_user = aw.ax_user;
            b_beats.push(b);

            aw_pending_resp.pop();
        }

        bool has_w_beat()
        {
            return !w_beat_requests.empty();
        }

        w_beat_request_t get_next_w_beat()
        {
            assert(has_w_beat());
            w_beat_request_t w = w_beat_requests.front();
            w_beat_requests.pop();
            return w;
        }

        bool has_r_beat()
        {
            return !ar_beats.empty();
        }

        r_beat_request_t get_next_r_beat()
        {
            assert(has_r_beat());

            axi_ax_beat_t &ar = ar_beats.front();
            uint32_t data_size = pow(2, ar.ax_size);
            
            bool is_last = ar.ax_len == 0;
            //printf("AXISlave AR beat ax_len: %u; is_last: %u\n", (uint32_t) ar.ax_len, (uint32_t) is_last);
            r_beat_request_t req;
            req.addr = ar.ax_addr;
            req.data_size = data_size;

            req.r_beat.r_resp = AXI_RESP_OKAY;
            req.r_beat.r_last = is_last;
            req.r_beat.r_id = ar.ax_id;
            req.r_beat.r_user = ar.ax_user;

            // AXI_BURST_WRAP is not implemented
            assert(ar.ax_burst == AXI_BURST_FIXED || ar.ax_burst == AXI_BURST_INCR);
            if (ar.ax_burst == AXI_BURST_INCR)
            {
                ar.ax_addr += data_size;
            }

            //ax_len = n_beats + 1;
            if (is_last)
            {
                ar_beats.pop();
            }
            else
            {
                ar.ax_len--;
            }

            return req;
        }

    private:
        void aw_posedge()
        {
            *port.aw_ready = 0;

            bool can_accept_aw = aw_beats_buffer_size == 0 || aw_beats.size() < aw_beats_buffer_size;
            if (*port.aw_valid && can_accept_aw)
            {
                axi_ax_beat_t aw_beat;

                aw_beat.ax_addr = *port.aw_addr;
                aw_beat.ax_atop = *port.aw_atop;
                aw_beat.ax_burst = *port.aw_burst;
                aw_beat.ax_cache = *port.aw_cache;
                aw_beat.ax_id = *port.aw_id;
                aw_beat.ax_len = *port.aw_len;
                aw_beat.ax_lock = *port.aw_lock;
                aw_beat.ax_prot = *port.aw_prot;
                aw_beat.ax_qos = *port.aw_qos;
                aw_beat.ax_region = *port.aw_region;
                aw_beat.ax_size = *port.aw_size;
                aw_beat.ax_user = *port.aw_user;
                aw_beat.offset = 0;

                aw_beats.push(aw_beat);

                *port.aw_ready = 1;
            }
        }

        void aw_negedge()
        {
            // Nothing to do here
        }

        void ar_posedge()
        {
            *port.ar_ready = 0;

            bool can_accept_ar = ar_beats_buffer_size == 0 || ar_beats.size() < ar_beats_buffer_size;
            if (*port.ar_valid && can_accept_ar)
            {
                axi_ax_beat_t ar_beat;

                ar_beat.ax_addr = *port.ar_addr;
                ar_beat.ax_burst = *port.ar_burst;
                ar_beat.ax_cache = *port.ar_cache;
                ar_beat.ax_id = *port.ar_id;
                ar_beat.ax_len = *port.ar_len;
                ar_beat.ax_lock = *port.ar_lock;
                ar_beat.ax_prot = *port.ar_prot;
                ar_beat.ax_qos = *port.ar_qos;
                ar_beat.ax_region = *port.ar_region;
                ar_beat.ax_size = *port.ar_size;
                ar_beat.ax_user = *port.ar_user;

                ar_beat.offset = 0;

                ar_beats.push(ar_beat);

                *port.ar_ready = 1;
            }
        }

        void ar_negedge()
        {
            // Nothing to do here
        }

        void w_posedge()
        {
            *port.w_ready = 0;

            bool can_accept_w = w_beats_buffer_size == 0 || w_beat_requests.size() < w_beats_buffer_size;
            if (*port.w_valid && can_accept_w)
            {
                assert(!aw_beats.empty());
                axi_ax_beat_t &aw = aw_beats.front();
                unsigned int strb_low  = (unsigned int) ((*port.w_strb));
                unsigned int strb_high = (unsigned int) ((*port.w_strb) >> 32);
                uint32_t data_size = __builtin_popcount(strb_low) + __builtin_popcount(strb_high);

                w_beat_request_t req;
                req.addr = aw.ax_addr + aw.offset;
                req.data_size = data_size;
                req.w_beat.w_strb = *port.w_strb;
                req.w_beat.w_user = *port.w_user;
                req.w_beat.w_last = *port.w_last;

                aw.offset += data_size;

                memcpy(req.w_beat.w_data, port.w_data, AXI_SW);

                w_beat_requests.push(req);

                if (*port.w_last == 1)
                {
                    aw_pending_resp.push(aw);
                    aw_beats.pop();
                }

                *port.w_ready = 1;
            }
        }

        void w_negedge()
        {
            // Nothing to do here
        }

        void r_posedge()
        {
            if (r_wait)
            {
                return;
            }

            *port.r_valid = 0;

            if (r_beats.empty()) 
            {
                return;
            }

            axi_r_beat_t &r = r_beats.front();
            

            *port.r_resp = r.r_resp;
            *port.r_last = r.r_last;
            *port.r_id = r.r_id;
            *port.r_user = r.r_user;
            memcpy(port.r_data, r.r_data, AXI_SW);

            *port.r_valid = 1;
            r_beats.pop();
        }

        void r_negedge()
        {
            //R_READY can be function of R_VALID, so let's see if we have it set already
            r_wait = false;
            if (*port.r_valid && !(*port.r_ready))
            {
                r_wait = true;
            }
        }

        void b_posedge()
        {
            if (b_wait)
            {
                return;
            }

            *port.b_valid = 0;

            if (b_beats.empty()) 
            {
                return;
            }

            axi_b_beat_t &b = b_beats.front();
            
            *port.b_resp = b.b_resp;
            *port.b_id = b.b_id;
            *port.b_user = b.b_user;
            b_beats.pop();

            *port.b_valid = 1;
        }

        void b_negedge()
        {
            //B_READY can be function of B_VALID, so let's see if we have it set already
            b_wait = false;
            if (*port.b_valid && !(*port.b_ready))
            {
                b_wait = true;
            }
        }
    };

} // namespace PsPIN