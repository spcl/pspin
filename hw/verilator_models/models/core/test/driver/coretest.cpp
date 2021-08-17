
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


#include <stdio.h>
#include <spin_hw_conf.h>
#include <pspincoresim.hpp>
#include <assert.h>
#include <stdint.h>

#define PATH_MAX 1024
#define SLM_PATH "build/slm_files/"
#define HANDLERS_BINARY "build/test"
#define NUM_PACKETS 8

using namespace PsPIN;

typedef struct packet 
{
    uint32_t id;
    uint8_t data[1020];
} packet_t;

static PsPINCoreSim *sim;
static her_descr_t her;
static uint32_t tick;
static packet_t pkt_out_buff;

char slm_path[PATH_MAX];

double sc_time_stamp()
{   // Called by $time in Verilog
    return tick;
}

const char* get_slm_path()
{
    return slm_path;
}

void init_her(her_descr_t *her, std::string hh_name, std::string ph_name, std::string th_name, uint32_t msgid, uint32_t addr, uint32_t size, bool eom)
{
    her->msgid = msgid;
    her->eom = eom;
    her->her_addr = addr;
    her->her_size = size;
    her->xfer_size = size;

    uint32_t hh_addr, ph_addr, th_addr;
    size_t hh_size, ph_size, th_size;
    PsPINCoreSim::findHandlerByName(HANDLERS_BINARY, hh_name.c_str(), &hh_addr, &hh_size);
    PsPINCoreSim::findHandlerByName(HANDLERS_BINARY, ph_name.c_str(), &ph_addr, &ph_size);
    PsPINCoreSim::findHandlerByName(HANDLERS_BINARY, th_name.c_str(), &th_addr, &th_size);
    her->mpq_meta.hh_addr = hh_addr;
    her->mpq_meta.ph_addr = ph_addr;
    her->mpq_meta.th_addr = th_addr;
    her->mpq_meta.hh_size = hh_size;
    her->mpq_meta.ph_size = ph_size;
    her->mpq_meta.th_size = th_size;
 
    her->mpq_meta.handler_mem_addr = L2_BASE_ADDR;
    her->mpq_meta.handler_mem_size = 4096;
    her->mpq_meta.host_mem_addr = 0xcafebebe;
    her->mpq_meta.host_mem_size = 1048576;

    for (int i=0; i<NUM_CLUSTERS; i++) {
        her->mpq_meta.scratchpad_addr[i] = L1_SCRATCHPAD_ADDR(i);
        her->mpq_meta.scratchpad_size[i] = L1_SCRATCHPAD_SIZE;
    }
}

static void her_complete(her_descr_t *her) 
{
    printf("completed!\n");
    sim->shutdown();
}


static void packet_write_complete() 
{
    assert(sim->canSendHER());
    init_her(&her, "test_hh", "test_ph", "test_th", 0, L2_PKT_BUFF_START, sizeof(packet_t), 1);

    auto cb = std::bind(&her_complete, &her);
    sim->sendHER(&her, cb);
}

static void packet_read_complete(PsPINCoreSim::CommandID cmd_id)
{
    uint32_t pkt_id = pkt_out_buff.id;
    printf("Read packet from PsPIN memory. ID: 0x%x\n", pkt_id);
    sim->sendNICCommandCompletion(cmd_id);
}

static void nic_command_handler(PsPINCoreSim::NICCommand cmd)
{
    printf("Got NIC command: dst: %d; src_addr; 0x%x; size: %d\n", cmd.nid, cmd.source_addr, cmd.length);
    auto cb = std::bind(packet_read_complete, cmd.cmd_id);
    sim->nicMemRead(cmd.source_addr, (uint8_t*) &pkt_out_buff, cmd.length, cb);
}

int main(int argc, char** argv)
{

    snprintf(slm_path, PATH_MAX, "%s/", SLM_PATH);

    uint32_t pktbuff_start_addr = L2_PKT_BUFF_START;
    sim = new PsPINCoreSim("test.vcd");
    tick = 0;

    sim->setNICCommandCallback(nic_command_handler);

    packet_t pkt;
    pkt.id = 0xdeadbeef;

    assert(sim->canNICWrite());
    sim->nicMemWrite(pktbuff_start_addr, (uint8_t*) &pkt, sizeof(packet_t), packet_write_complete);

    uint8_t done = 0;
    while (!done) {
        sim->step(&done);
        tick++;
    }

    return 0;
}