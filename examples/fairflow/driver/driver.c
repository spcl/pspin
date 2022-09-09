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

#include <stdint.h>
#include <stdio.h>
#include <sys/types.h>
#include <unistd.h>
#include <string.h>
#include <assert.h>

#include "gdriver.h"

#define PKT_SIZE 2048
#define MAX_FLOWS 100

#define USE_TRACE

uint32_t fill_packet(uint32_t msg_idx, uint32_t pkt_idx, uint8_t *pkt_buff, uint32_t max_pkt_size, uint32_t* l1_pkt_size)
{   
    uint32_t *pkt_buff_int = (uint32_t*) pkt_buff;
    *pkt_buff_int = pkt_idx;
    return max_pkt_size;
}

int main(int argc, char**argv)
{
    const char *handlers_file="build/empty";
    const char *hh=NULL;// "empty_hh";
    const char *ph="empty_ph";
    const char *th=NULL;// "empty_th";

    //const char *trace_file="traces/trace_exp1.txt";
    const char *trace_file="traces/trace_real.csv";

    gdriver_init(argc, argv, handlers_file, hh, ph, th);
    
#ifndef USE_TRACE
    gdriver_set_packet_fill_callback(fill_packet);
#else
    
    gdriver_set_packet_fill_callback(NULL);
   
    
    //read trace
    FILE * fp;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;

    fp = fopen(trace_file, "r");
    if (fp == NULL) {
        printf("Trace file not found!\n");
        exit(EXIT_FAILURE);
    }

    uint32_t flow_pkt_count[MAX_FLOWS];
    for (int i=0; i<MAX_FLOWS; i++) flow_pkt_count[i] = 0;

    uint8_t* pkt_buffer = (uint8_t*) malloc(PKT_SIZE);
    while ((read = getline(&line, &len, fp)) != -1) {
        
        uint32_t flow_id = atoi(strtok(line, ","));
        uint32_t num_pkts_flow = atoi(strtok(NULL, ","));
        uint32_t delay = atoi(strtok(NULL, ","));
        uint32_t pkt_size = atoi(strtok(NULL, ",")); 

        //optional 
        uint32_t handler_cost = 0;
        char *handler_cost_str = strtok(NULL, ",");
        if (handler_cost_str!=NULL) { handler_cost = atoi(handler_cost_str); }
      
        uint32_t* pkt_ptr_int = (uint32_t *) pkt_buffer;
        *pkt_ptr_int = handler_cost;

        assert(pkt_size <= PKT_SIZE);        
        assert(flow_id < MAX_FLOWS);

        flow_pkt_count[flow_id]++;
        uint8_t is_last = (flow_pkt_count[flow_id] == num_pkts_flow);
        printf("Flow id: %lu; diff: %lu; pkts: %lu/%lu; is_last: %u; handler_cost: %u\n", flow_id, delay, flow_pkt_count[flow_id], num_pkts_flow, is_last, handler_cost);

        gdriver_enqueue_pkt(flow_id, pkt_buffer, pkt_size, pkt_size, is_last, delay);
        
    }

    pspinsim_packet_eos();
#endif

    printf("Run!\n");

    gdriver_run();

    return (gdriver_fini()) ? EXIT_SUCCESS : EXIT_FAILURE;
}
