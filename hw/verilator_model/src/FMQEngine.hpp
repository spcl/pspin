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
            FMQ()
            : state(Idle), 
              eom_seen(false), 
              task_in_flight(0), 
              fmq_idx(0), 
              her_ta_sum(0), 
              feedback_ta_sum(0), 
              last_her_time(0), 
              last_feedback_time(0),
              num_hers_seen(0),
              num_feedback_seen(0),
              bytes_seen(0),
              expected_time_next_pkt(0),
              last_fair_share(0)
            {}

            void configure(uint32_t fmq_idx, uint32_t prio)
            {
                assert(prio>0);
                this->fmq_idx = fmq_idx;
                this->prio = prio;
            }

            uint32_t get_fmq_idx()
            {
                return fmq_idx;
            }

            void fmq_init(HER& h)
            {
                if (h.her_meta_hh_addr != 0) state = HHReady;
                else state = PHReady;

                has_th = h.her_meta_th_addr != 0;
            }

            bool push_her(HER& h, uint64_t simtime) {
                bool was_idle = false;

                register_her(h, simtime);
                if (state==Idle) 
                {
                    was_idle=true; 
                    fmq_init(h);
                } 

                if (h.her_is_eom) eom_seen = 1;
                hers.push(h);
                print_state(simtime, "NEW_HER");
                expected_time_next_pkt = simtime + get_current_her_ta();
                return was_idle;
            }

            void register_her(HER& h, uint64_t simtime)
            {
                if (state!=Idle) 
                {
                    her_ta_sum += (simtime - last_her_time);
                }

                num_hers_seen++;
                bytes_seen += h.her_size;
                last_her_time = simtime;
            }

            double get_current_her_ta() 
            {
                if (num_hers_seen==1) return 0;
                return (double) her_ta_sum / (num_hers_seen-1); 
            }

            double get_current_pkt_size_avg()
            {
                return (double) bytes_seen / num_hers_seen;
            }

            uint32_t get_in_flight()
            {
                return task_in_flight;
            }

            double get_in_flight_avg()
            {
                return (double) task_in_flight_sum / task_in_flight_measurements;
            }

            bool handle_feedback(uint64_t simtime) {
                assert(task_in_flight>0);
                task_in_flight--;
                if (state == HHDraining) state = PHReady;
                else if (state == PHDraining && task_in_flight == 0) {
                    if (has_th) state = THReady;
                    else state = Idle;
                }
                else if (state == THReady) state = Idle;
                print_state(simtime, "FEEDBACK");
                return state == Idle;
            }

            Task produce_next_task(uint64_t simtime) 
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
                    if (eom_seen && hers.size() == 1) 
                    {
                        pop_her = !has_th;
                        state = PHDraining;
                    }
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


                //printf("FMQ task idx: %u; state: %u; trigger_feedback: %u\n", fmq_idx, state, pop_her);
                print_state(simtime, "TASK");
                if (pop_her) hers.pop();

                return t;
            }

            void print_state(uint64_t simtime, std::string label)
            {                
                printf("%lu %s idx=%u; prio=%u; state=%u; her_ta=%lf; task_in_flight=%u; bytes_seen=%lu; num_hers=%u; queue_len=%u; last_fair_share=%lf; last_slack=%lf; is_warm=%u; expected_time_next_pkt=%u;\n", simtime, label.c_str(), fmq_idx, prio, state, get_current_her_ta(), task_in_flight, bytes_seen, num_hers_seen, hers.size(), last_fair_share, last_slack, (uint32_t) is_warm(simtime), expected_time_next_pkt);
            }

            bool is_idle() {
                return state == Idle;
            }

            bool is_warm(uint64_t simtime)
            {
                return has_active_state() && simtime <= expected_time_next_pkt*1.5;
            }

            bool has_active_state()
            {
                return (state == HHReady || state == PHReady || state == THReady);
            }

            bool is_ready() 
            {
                return !hers.empty() && has_active_state();
            }

            bool is_schedulable(double fair_share, double slack = 0)
            {
                return (fair_share < 0 || slack > 0 || task_in_flight <= fair_share);
            }

            void register_stat(double fair_share, double slack)
            {
                task_in_flight_sum += task_in_flight;
                task_in_flight_measurements++;
            }

            void set_fair_share(double fair_share) 
            {
                last_fair_share = fair_share;
            }

            void set_slack(double slack)
            {
                last_slack = slack;
            }

            bool is_potential_bottleneck()
            {
                return task_in_flight >= last_fair_share;
            }

            uint32_t get_prio()
            {
                return prio;
            }

        private:
            enum State {Idle=0, HHReady, HHDraining, PHReady, PHDraining, THReady};

        private:
            std::queue<HER> hers;
            State state;
            bool eom_seen;
            bool has_th;
            uint32_t task_in_flight;
            uint32_t fmq_idx;

            uint64_t last_her_time;
            uint64_t last_feedback_time;
            uint64_t her_ta_sum;
            uint64_t feedback_ta_sum;
            uint64_t num_hers_seen;
            uint64_t num_feedback_seen;
            uint64_t bytes_seen;
            uint32_t prio;
            uint64_t expected_time_next_pkt;
            double last_fair_share;
            double last_slack;

            uint32_t task_in_flight_sum;
            uint32_t task_in_flight_measurements;
        };

        class FMQArbiter {
        public:
            virtual FMQ& get_next(uint64_t simtime, bool &found_one) = 0;

            FMQArbiter(std::vector<FMQ> &fmqs)
            : fmqs(fmqs)
            {}

        protected:
            std::vector<FMQ> &fmqs;
        };

        class FMQRRArbiter : public FMQArbiter {
        public:
            FMQRRArbiter(std::vector<FMQ> &fmqs)
            : FMQArbiter(fmqs), next(0)
            {}

            FMQ& get_next(uint64_t simtime, bool &found_one) 
            {   
                found_one = false;
                for (int i=0; i<fmqs.size(); i++) {
                    FMQ& curr = fmqs[next];
                    next = (next + 1) % fmqs.size();
                    if (curr.is_ready()) {
                        found_one = true;
                        return curr;
                    }
                }

                return fmqs[0];
            }

        private:
            uint32_t next;
        };

        class FMQPrioArbiter : public FMQArbiter {
        public:
            FMQPrioArbiter(std::vector<FMQ> &fmqs)
            : FMQArbiter(fmqs)
            {}

            FMQ& get_next(uint64_t simtime, bool &found_one) 
            {   
                found_one = false;

                uint32_t max_prio = 0;
                uint32_t max_prio_idx = 0;

                for (int i=0; i<fmqs.size(); i++) 
                {   
                    FMQ& curr = fmqs[i];
                    if (curr.is_ready() && curr.get_prio() > max_prio) {
                        max_prio = curr.get_prio();
                        found_one = true;
                        max_prio_idx = i;    
                    }
                }

                return fmqs[max_prio_idx];
            }
        };

        class FMQPrioFairArbiter : public FMQArbiter {
        public:
            FMQPrioFairArbiter(std::vector<FMQ> &fmqs, bool be_fair = true) 
            : FMQArbiter(fmqs), be_fair(be_fair)
            {}

            uint32_t get_prio_sum(uint64_t simtime)
            {
                uint32_t sum_active_prio = 0;
                for (int i=0; i<fmqs.size(); i++) 
                { 
                    if (fmqs[i].is_ready() || fmqs[i].is_warm(simtime)) sum_active_prio += fmqs[i].get_prio();     
                }

                return sum_active_prio;
            }

            uint32_t get_bottleneck_prio_sum(uint64_t simtime)
            {
                uint32_t sum_active_prio = 0;
                for (int i=0; i<fmqs.size(); i++) 
                { 
                    bool consider_fmq = fmqs[i].is_ready() || fmqs[i].is_warm(simtime);
                    consider_fmq = consider_fmq && fmqs[i].is_potential_bottleneck();
                    if (consider_fmq) sum_active_prio += fmqs[i].get_prio();     
                }

                return sum_active_prio;
            }

            FMQ& get_next(uint64_t simtime, bool &found_one) 
            {
                uint32_t num_pe = NUM_CORES * NUM_CLUSTERS;
                uint32_t sum_active_prio = get_prio_sum(simtime);
                found_one = false;


                uint32_t max_prio = 0;
                uint32_t max_prio_idx = 0;
                double max_prio_fair_share = 0; //stats only
                double max_prio_slack = 0; //stats only

                for (int i=0; i<fmqs.size(); i++) 
                {   
                    FMQ& curr = fmqs[i];
                    double fair_share = num_pe * ((double) curr.get_prio() / sum_active_prio);
                    curr.set_fair_share(fair_share);
                    curr.set_slack(0);
                    if (curr.is_ready() && curr.is_schedulable(fair_share) && curr.get_prio() > max_prio) {
                        max_prio = curr.get_prio();
                        max_prio_idx = i;    
                        max_prio_fair_share = fair_share;
                        max_prio_slack = 0;
                    }

                }


                if (max_prio==0 && be_fair) {
                    // in this case no flow can be scheduled within their fair share.
                    // we may still have some budget to redistribute

                    // get sum of in flight packets
                    uint32_t currently_in_flight = 0;
                    for (int i=0; i<fmqs.size(); i++) 
                    {
                        FMQ& curr = fmqs[i];
                        currently_in_flight += curr.get_in_flight();
                    }

                    // see of there are bottlenecks
                    uint32_t bottleneck_prio_sum = get_bottleneck_prio_sum(simtime);

                    // if there is budget and there are bottlnecks
                    if (bottleneck_prio_sum > 0 && currently_in_flight < num_pe)
                    {

                        uint32_t slack_budget = num_pe - currently_in_flight;

                        for (int i=0; i<fmqs.size(); i++) 
                        {
                            FMQ& curr = fmqs[i];

                            // we care only about bottlenecks here
                            if (!curr.is_potential_bottleneck() || !curr.is_ready()) continue;

                            double fair_share = num_pe * ((double) curr.get_prio() / sum_active_prio);
                            double slack = slack_budget * ((double) curr.get_prio() / bottleneck_prio_sum);
                            bool is_schedulable = curr.is_ready() && curr.is_schedulable(fair_share, slack);
                            curr.set_slack(slack);
                            printf("Trying to schedule bottleneck flow %d (prio: %u): slack_budget: %u; bottleneck_prio_sum: %u; sum_active_prio: %u; fair_share: %lf; slack: %lf; is_ready: %ul is_schedulable: %u; in_flight: %u\n", i, curr.get_prio(), slack_budget, bottleneck_prio_sum, sum_active_prio, fair_share, slack, (uint32_t) curr.is_ready(), (uint32_t) is_schedulable, curr.get_in_flight());
                            if (is_schedulable && curr.get_prio() > max_prio) {
                                max_prio = curr.get_prio();
                                max_prio_idx = i;    
                                max_prio_fair_share = fair_share;
                                max_prio_slack = slack;
                            }
                        }
                    }
                }

                if (max_prio>0)
                {
                    fmqs[max_prio_idx].register_stat(max_prio_fair_share, max_prio_slack);
                    found_one = true;
                }

                return fmqs[max_prio_idx];
            }

        private:
            bool be_fair;
        };

    public:

        FMQEngine(fmq_control_port_concrete_t& ni_port, task_control_port_t& sched_port, uint32_t num_fmqs = 1024, bool fair_mode=true) 
        : ni_port(ni_port), sched_port(sched_port), feedback_buffer(1), feedbacks_to_send(0), num_fmqs(num_fmqs), active_fmqs(0)
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
            for (uint32_t i=0; i<num_fmqs; i++) { fmqs[i].configure(i, i+1); }
            // fmqs[0].configure(0, 1024);
            // fmqs[1].configure(1, 1024);
            // fmqs[2].configure(2, 512);
            // fmqs[3].configure(3, 1);
            // fmqs[4].configure(4, 1024);
            // fmqs[10].configure(10, 1);


            //override priorities (format: FLOW=PRIO;FLOW=PRIO;...)
            char* prio_override_env = getenv("PRIO_OVERRIDE");
            if (prio_override_env)
            {
                char* token;
                char* save_ptr = prio_override_env;
            
                while ((token = strtok_r(save_ptr, ";", &save_ptr)))
                {
                    uint32_t flow_id = atoi(strtok(token, "="));
                    uint32_t prio_val = atoi(strtok(NULL, "="));

                    printf("FMQ overriding priority of flow %u to %u\n", flow_id, prio_val);
                    assert(flow_id < num_fmqs);

                    fmqs[flow_id].configure(flow_id, prio_val);
                }
            
            }

            //configure arbiter
            char* arbiter_type_env = getenv("FMQ_ARBITER_TYPE");
            if (arbiter_type_env!=NULL){
                if (!strcmp(arbiter_type_env, "RR")) 
                {
                    printf("FMQ: RR arbiter\n");
                    fmq_arbiter = new FMQRRArbiter(fmqs);
                }
                else if (!strcmp(arbiter_type_env, "PRIO"))
                {
                    printf("FMQ: PRIO arbiter\n");
                    fmq_arbiter = new FMQPrioArbiter(fmqs);
                }
                else if (!strcmp(arbiter_type_env, "PRIO-FAIR-STRICT"))
                {
                    printf("FMQ: PRIO arbiter (strict)\n");
                    fmq_arbiter = new FMQPrioFairArbiter(fmqs, false);
                }
                else if (!strcmp(arbiter_type_env, "PRIO-FAIR-DYN"))
                {
                    printf("FMQ: PRIO arbiter (dynamic)\n");
                    fmq_arbiter = new FMQPrioFairArbiter(fmqs, true);
                }
                else 
                {
                    assert(0);
                }
            } 
            else 
            {
                printf("FMQ: RR arbiter (default)\n");
                fmq_arbiter = new FMQRRArbiter(fmqs);
            }
        }

        ~FMQEngine() 
        {
            delete fmq_arbiter;
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

                bool was_idle = get_fmq(new_her.her_msgid).push_her(new_her, sim_time());
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

                bool become_idle = get_fmq(*sched_port.feedback_msgid_i).handle_feedback(sim_time());
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
            if (sched_not_ready) {
                //printf("SCHEDULER STALLING!\n");   
                return;
            }
            *sched_port.task_valid_o = 0;

            bool found_one = false;
            FMQ& fmq_to_sched = fmq_arbiter->get_next(sim_time(), found_one);
            if (!found_one) return;

            Task task = fmq_to_sched.produce_next_task(sim_time());
            
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

        //FMQRRArbiter fmq_arbiter;
        FMQArbiter *fmq_arbiter;
        uint32_t num_fmqs;
        uint32_t active_fmqs;
    };

}
