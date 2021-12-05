#pragma once

#include "Vpspin_verilator.h"
#include "verilated.h"
#include "SimModule.hpp"
#include "AXIMaster.hpp"
#include "pspin.hpp"
#include "spin.h"
#include "pspinsim.h"


namespace PsPIN
{


    class FMQEngine : public SimModule
    {


    public:

        template <typename T>
        class Buffer
        {
        private:
            std::queue<T> elements;
            uint32_t capacity;

        public:
            Buffer<T>(uint32_t capacity) : capacity(capacity)
            {}

            bool is_full()
            {
                return elements.size() >= capacity;
            }

            bool is_empty() 
            {
                return elements.empty();
            }

            void push(T el)
            {
                assert(!is_full());
                elements.push(el);
            }

            T& front()
            {
                assert(!is_empty());
                return elements.front();
            }

            void pop() 
            {
                assert(!is_empty());
                elements.pop();
            }
        };

        class HER {
        public:
            uint16_t        her_msgid;
            uint8_t         her_is_eom;
            mem_addr_t      her_addr;
            mem_size_t      her_size;
            mem_size_t      her_xfer_size;
            mem_addr_t      her_meta_handler_mem_addr;
            mem_size_t      her_meta_handler_mem_size;
            host_addr_t     her_meta_host_mem_addr;
            mem_size_t      her_meta_host_mem_size;
            mem_addr_t      her_meta_hh_addr;
            mem_size_t      her_meta_hh_size;
            mem_addr_t      her_meta_ph_addr;
            mem_size_t      her_meta_ph_size;
            mem_addr_t      her_meta_th_addr;
            mem_size_t      her_meta_th_size;
            mem_addr_t      her_meta_scratchpad_0_addr;
            mem_size_t      her_meta_scratchpad_0_size;
            mem_addr_t      her_meta_scratchpad_1_addr;
            mem_size_t      her_meta_scratchpad_1_size;
            mem_addr_t      her_meta_scratchpad_2_addr;
            mem_size_t      her_meta_scratchpad_2_size;
            mem_addr_t      her_meta_scratchpad_3_addr;
            mem_size_t      her_meta_scratchpad_3_size;
        };

        class Feedback 
        {
        public:
            uint16_t        feedback_msgid;
            uint32_t        feedback_her_addr;
            uint32_t        feedback_her_size;
        };


        class Task 
        {
        public:
            uint16_t    msgid;
            mem_addr_t  pkt_addr;
            mem_size_t  pkt_size;
            mem_addr_t  l2_mem_addr;
            mem_size_t  l2_mem_size;
            host_addr_t host_mem_addr;
            mem_size_t  host_mem_size;
            mem_addr_t  handler_addr;
            mem_size_t  handler_size;
            mem_addr_t  scratchpad_addr[NUM_CLUSTERS];
            mem_size_t  scratchpad_size[NUM_CLUSTERS];
            uint8_t     trigger_feedback;
        };

        class FMQ {
        public:
            FMQ(): state(Idle), eom_seen(false), task_in_flight(0)
            {}

            void fmq_init(HER& h)
            {
                if (h.her_meta_hh_addr != 0) state = HHReady;
                else state = PHReady;

                has_th = h.her_meta_th_addr != 0;
            }

            bool push_her(HER& h) {
                bool was_idle = false;
                if (state==Idle) 
                {
                    was_idle=true; 
                    fmq_init(h);
                }

                if (h.her_is_eom) eom_seen = 1;

                hers.push(h);

                return was_idle;
            }

            bool handle_feedback() {
                assert(task_in_flight>0);
                task_in_flight--;
                if (state == HHDraining) state = PHReady;
                else if (state == PHDraining && task_in_flight == 0) {
                    if (has_th) state = THReady;
                    else state = Idle;
                }
                else if (state == THReady) state = Idle;
                printf("FMQ feedback; state: %u\n", state);
                return state == Idle;
            }

            Task produce_next_task() 
            {
                assert(this->is_ready());
                task_in_flight++;

                HER& h = hers.front();

                Task t;
                bool pop_her = false;

                if (state == HHReady) {
                    t.handler_addr = h.her_meta_hh_addr;
                    state = HHDraining;
                } else if (state == PHReady) {
                    t.handler_addr = h.her_meta_ph_addr;
                    
                    // if this is the last task we send, then prepare for completion
                    if (eom_seen && hers.size() == 1) state = PHDraining;
                    else pop_her = true;

                } else {
                    t.handler_addr = h.her_meta_th_addr;
                    pop_her = true;
                }
                
                t.handler_size = 4096;
                t.host_mem_addr = h.her_meta_host_mem_addr;
                t.host_mem_size = h.her_meta_host_mem_size;
                t.l2_mem_addr = h.her_meta_handler_mem_addr;
                t.l2_mem_size = h.her_meta_handler_mem_size;
                t.msgid = h.her_msgid;
                t.pkt_addr = h.her_addr;
                t.pkt_size = h.her_xfer_size;
                t.scratchpad_addr[0] = h.her_meta_scratchpad_0_addr;
                t.scratchpad_size[0] = h.her_meta_scratchpad_0_size;
                t.scratchpad_addr[1] = h.her_meta_scratchpad_1_addr;
                t.scratchpad_size[1] = h.her_meta_scratchpad_1_size;
                t.scratchpad_addr[2] = h.her_meta_scratchpad_2_addr;
                t.scratchpad_size[2] = h.her_meta_scratchpad_2_size;
                t.scratchpad_addr[3] = h.her_meta_scratchpad_3_addr;
                t.scratchpad_size[3] = h.her_meta_scratchpad_3_size;
                t.trigger_feedback = pop_her;


                printf("FMQ state=%u; trigger_feedback=%u\n", state, pop_her);
                if (pop_her) hers.pop();

                return t;
            }

            bool is_idle() {
                return state == Idle;
            }

            bool is_ready() {
                return !hers.empty() && (state == HHReady || state == PHReady || state == THReady);
            }

        private:
            enum State {Idle=0, HHReady, HHDraining, PHReady, PHDraining, THReady};

        private:
            std::queue<HER> hers;
            State state;
            bool eom_seen;
            bool has_th;
            uint32_t task_in_flight;
        };

        class FMQRRArbiter {

        public:
            FMQRRArbiter(std::vector<FMQ> &fmqs)
            : fmqs(fmqs), next(0)
            {}

            bool is_one_ready()
            {
                for (int i=0; i<fmqs.size(); i++)
                {
                    if (fmqs[i].is_ready()) return true;
                }
                return false;
            }

            FMQ& get_next() 
            {
                for (int i=0; i<fmqs.size(); i++) {
                    FMQ& curr = fmqs[next];
                    next = (next + 1) % fmqs.size();
                    if (curr.is_ready()) return curr;
                }
                assert(0);
            }

        private:
            std::vector<FMQ> &fmqs;
            uint32_t next;
        };

    public:

        FMQEngine(fmq_control_port_concrete_t& ni_port, task_control_port_t& sched_port, uint32_t num_fmqs = 1024) 
        : ni_port(ni_port), sched_port(sched_port), feedback_buffer(1), feedbacks_to_send(0), fmq_arbiter(fmqs), num_fmqs(num_fmqs), active_fmqs(0)
        {
            //clean NI port state
            this->ni_port.her_ready_o = 1;
            this->ni_port.feedback_valid_o = 0;

            //clean SCHED port state
            *this->sched_port.task_valid_o = 0;
            *this->sched_port.feedback_ready_o = 0;

            sched_not_ready = false;
            ni_not_ready = false;

            fmqs.resize(num_fmqs);
        }

        void posedge()
        {
            // in this order there is at least one cycle between the receiving of a HER and 
            // the scheduling of the respective task
            // oh well, if the compiler doesn't reorder these two
            produce_output_posedge();
            check_new_tasks_posedge();

            // if we keep this call order, a feedback goes through 
            // in a single cycle if it does not stall (as it happens 
            // in the cycle accurate simulation)
            check_new_feedbacks_posedge();
            progress_feedbacks_posedge();

            // forward the active signal to the NIC
            ni_port.pspin_active_o = *sched_port.pspin_active_i;

            check_termination_posedge();
        }

        void negedge()
        {
            progress_feedbacks_negedge();
            produce_output_negedge();
        }

        void check_new_tasks_posedge() 
        {
            if (ni_port.her_ready_o && ni_port.her_valid_i) 
            {
                SIM_PRINT("Received HER from NIC\n");
                HER new_her;
                new_her.her_msgid                   = ni_port.her_msgid_i;
                new_her.her_is_eom                  = ni_port.her_is_eom_i;
                new_her.her_addr                    = ni_port.her_addr_i;
                new_her.her_size                    = ni_port.her_size_i;
                new_her.her_xfer_size               = ni_port.her_xfer_size_i;
                new_her.her_meta_handler_mem_addr   = ni_port.her_meta_handler_mem_addr_i;
                new_her.her_meta_handler_mem_size   = ni_port.her_meta_handler_mem_size_i;
                new_her.her_meta_host_mem_addr      = ni_port.her_meta_host_mem_addr_i;
                new_her.her_meta_host_mem_size      = ni_port.her_meta_host_mem_size_i;
                new_her.her_meta_hh_addr            = ni_port.her_meta_hh_addr_i;
                new_her.her_meta_hh_size            = ni_port.her_meta_hh_size_i;
                new_her.her_meta_ph_addr            = ni_port.her_meta_ph_addr_i;
                new_her.her_meta_ph_size            = ni_port.her_meta_ph_size_i;
                new_her.her_meta_th_addr            = ni_port.her_meta_th_addr_i;
                new_her.her_meta_th_size            = ni_port.her_meta_th_size_i;
                new_her.her_meta_scratchpad_0_addr  = ni_port.her_meta_scratchpad_0_addr_i;
                new_her.her_meta_scratchpad_0_size  = ni_port.her_meta_scratchpad_0_size_i;
                new_her.her_meta_scratchpad_1_addr  = ni_port.her_meta_scratchpad_1_addr_i;
                new_her.her_meta_scratchpad_1_size  = ni_port.her_meta_scratchpad_1_size_i;
                new_her.her_meta_scratchpad_2_addr  = ni_port.her_meta_scratchpad_2_addr_i;
                new_her.her_meta_scratchpad_2_size  = ni_port.her_meta_scratchpad_2_size_i;
                new_her.her_meta_scratchpad_3_addr  = ni_port.her_meta_scratchpad_3_addr_i;
                new_her.her_meta_scratchpad_3_size  = ni_port.her_meta_scratchpad_3_size_i;

                bool was_idle = get_fmq(new_her.her_msgid).push_her(new_her);
                if (was_idle) active_fmqs++;
            }
        }

        void check_new_feedbacks_posedge()
        {
            *sched_port.feedback_ready_o = 0;
            if (feedback_buffer.is_full()) return;

            if (*sched_port.feedback_valid_i)
            {
                SIM_PRINT("Received feedback from scheduler\n");
                *sched_port.feedback_ready_o = 1;

                bool become_idle = get_fmq(*sched_port.feedback_msgid_i).handle_feedback();
                if (become_idle) active_fmqs--;

                Feedback f;
                f.feedback_her_addr = *sched_port.feedback_her_addr_i;
                f.feedback_her_size = *sched_port.feedback_her_size_i;
                f.feedback_msgid = *sched_port.feedback_msgid_i;

                feedback_buffer.push(f);
            }
        }

        void progress_feedbacks_posedge()
        {
            // ni_not_ready is the case where we are already trying to send a feedback but the NI is not ready (stalling on feedbacks)
            if (ni_not_ready) {
                return;
            }
            // the stall is over, let's reset the valid signal
            ni_port.feedback_valid_o = 0;

            // if we don't have nothing to send then return
            if (feedback_buffer.is_empty()) return;

            Feedback& f = feedback_buffer.front();
            ni_port.feedback_her_addr_o = f.feedback_her_addr;
            ni_port.feedback_her_size_o = f.feedback_her_size;
            ni_port.feedback_msgid_o = f.feedback_msgid;
            ni_port.feedback_valid_o = 1;

            SIM_PRINT("Sending feedback to NIC\n");

            feedback_buffer.pop();
        }

        void progress_feedbacks_negedge()
        {
            ni_not_ready = false;
            if (ni_port.feedback_valid_o && !(ni_port.feedback_ready_i))
            {
                ni_not_ready = true;
            }
        }

        void produce_output_posedge()
        {
            if (sched_not_ready) return;

            *sched_port.task_valid_o = 0;

            if (!fmq_arbiter.is_one_ready()) return;

            FMQ& fmq_to_sched = fmq_arbiter.get_next();

            Task task = fmq_to_sched.produce_next_task();
            
            //they should just be of the same type :(
            *sched_port.task_o.handler_addr = task.handler_addr;
            *sched_port.task_o.handler_size = task.handler_size;
            *sched_port.task_o.host_mem_addr = task.host_mem_addr;
            *sched_port.task_o.host_mem_size = task.host_mem_addr;
            *sched_port.task_o.l2_mem_addr = task.l2_mem_addr;
            *sched_port.task_o.l2_mem_size = task.l2_mem_size;
            *sched_port.task_o.msgid = task.msgid;
            *sched_port.task_o.pkt_addr = task.pkt_addr;
            *sched_port.task_o.pkt_size = task.pkt_size;
            *sched_port.task_o.scratchpad_addr[0] = task.scratchpad_addr[0];
            *sched_port.task_o.scratchpad_size[0] = task.scratchpad_size[0];
            *sched_port.task_o.scratchpad_addr[1] = task.scratchpad_addr[1];
            *sched_port.task_o.scratchpad_size[1] = task.scratchpad_size[1];
            *sched_port.task_o.scratchpad_addr[2] = task.scratchpad_addr[2];
            *sched_port.task_o.scratchpad_size[2] = task.scratchpad_size[2];
            *sched_port.task_o.scratchpad_addr[3] = task.scratchpad_addr[3];
            *sched_port.task_o.scratchpad_size[3] = task.scratchpad_size[3];
            *sched_port.task_o.trigger_feedback = task.trigger_feedback;

            *sched_port.task_valid_o = 1;

            SIM_PRINT("Sending task to scheduler\n");
        }

        void produce_output_negedge() 
        {
            sched_not_ready = false;
            if (*sched_port.task_valid_o && !(*sched_port.task_ready_i))
            {
                sched_not_ready = true;
            }
        }

        void check_termination_posedge()
        {
            if (ni_port.eos_i && active_fmqs==0) {
                printf("Simulation termination detected!\n");
                exit(0);
            }
        }

        void print_stats()
        {

        }

        FMQ& get_fmq(uint32_t msg_id)
        {
            assert(msg_id < num_fmqs);
            return fmqs[msg_id];
        }

    private:
        fmq_control_port_concrete_t& ni_port;
        task_control_port_t& sched_port;

        std::vector<FMQ> fmqs;

        bool ni_not_ready;
        bool sched_not_ready;
        Buffer<Feedback> feedback_buffer;

        uint32_t feedbacks_to_send;

        FMQRRArbiter fmq_arbiter;

        uint32_t num_fmqs;
        uint32_t active_fmqs;
    };

}