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
#include <stdlib.h>
#include <elf.h>
#include <sys/stat.h>
#include <sys/mman.h>

#include "Vpspin_verilator.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "AXIPort.hpp"
#include "NICInbound.hpp"
#include "NICOutbound.hpp"
#include "PCIeSlave.hpp"
#include "PCIeMaster.hpp"
#include "SimControl.hpp"
#include "FMQEngine.hpp"

#include "pspinsim.h"
#include "spin.h"
#include "pspin.hpp"

#define VCD_FILE "waves.vcd"


#define DEFAULT_NI_AXI_AW_BUFFER 32
#define DEFAULT_NI_AXI_W_BUFFER 32
#define DEFAULT_NI_AXI_B_BUFFER 32

#define NETWORK_G_200G 0.037252
#define NETWORK_G_400G 0.018626
#define PCIE_G_5_16 0.014782

#define DEFAULT_NO_AXI_AR_BUFFER 32
#define DEFAULT_NO_AXI_R_BUFFER 32
//#define DEFAULT_NO_NETWORK_G NETWORK_G_200G
#define DEFAULT_NO_NETWORK_G 0 
#define DEFAULT_NO_MAX_PKT_SIZE 2048
#define DEFAULT_NO_NET_PKT_QUEUE_LEN 32

#define DEFAULT_PCIE_SLV_AW_BUFFER_SIZE 32
#define DEFAULT_PCIE_SLV_W_BUFFER_SIZE 32
#define DEFAULT_PCIE_SLV_AR_BUFFER_SIZE 32
#define DEFAULT_PCIE_SLV_B_BUFFER_SIZE 32
#define DEFAULT_PCIE_SLV_R_BUFFER_SIZE 32
#define DEFAULT_PCIE_SLV_L 2
#define DEFAULT_PCIE_SLV_G PCIE_G_5_16

#define PATH_MAX 1024

using namespace PsPIN;

AXIPort<uint32_t, uint64_t> ni_mst;
ni_control_port_t ni_control;
AXIPort<uint32_t, uint64_t> no_mst;
no_cmd_port_t no_cmd;
AXIPort<uint64_t, uint64_t> pcie_slv_port;
AXIPort<uint32_t, uint64_t> pcie_mst_port;
fmq_control_port_concrete_t fmq_input_port;
task_control_port_t sched_port;

SimControl<Vpspin_verilator> *sim;
NICInbound<AXIPort<uint32_t, uint64_t>> *ni;
NICOutbound<AXIPort<uint32_t, uint64_t>> *no;
PCIeSlave<AXIPort<uint64_t, uint64_t>> *pcie_slv;
PCIeMaster<AXIPort<uint32_t, uint64_t>> *pcie_mst;
FMQEngine *fmq_eng;

char slm_path[PATH_MAX];

double sc_time_stamp()
{   // Called by $time in Verilog
    return sim->time();
}

extern "C" const char* get_slm_path()
{
    return slm_path;
}

int pspinsim_default_conf(pspin_conf_t *conf)
{
    conf->slm_files_path = NULL;
    conf->ni_conf.axi_aw_buffer = DEFAULT_NI_AXI_AW_BUFFER;
    conf->ni_conf.axi_w_buffer = DEFAULT_NI_AXI_W_BUFFER;
    conf->ni_conf.axi_b_buffer = DEFAULT_NI_AXI_B_BUFFER;

    conf->no_conf.axi_ar_buffer = DEFAULT_NO_AXI_AR_BUFFER;
    conf->no_conf.axi_r_buffer = DEFAULT_NO_AXI_R_BUFFER;
    conf->no_conf.network_G = DEFAULT_NO_NETWORK_G;
    conf->no_conf.max_pkt_size = DEFAULT_NO_MAX_PKT_SIZE;
    conf->no_conf.max_network_queue_len = DEFAULT_NO_NET_PKT_QUEUE_LEN;

    conf->pcie_slv_conf.axi_aw_buffer = DEFAULT_PCIE_SLV_AW_BUFFER_SIZE;
    conf->pcie_slv_conf.axi_w_buffer = DEFAULT_PCIE_SLV_W_BUFFER_SIZE;
    conf->pcie_slv_conf.axi_ar_buffer = DEFAULT_PCIE_SLV_AR_BUFFER_SIZE;
    conf->pcie_slv_conf.axi_b_buffer = DEFAULT_PCIE_SLV_B_BUFFER_SIZE;
    conf->pcie_slv_conf.axi_r_buffer = DEFAULT_PCIE_SLV_R_BUFFER_SIZE;
    conf->pcie_slv_conf.pcie_L = DEFAULT_PCIE_SLV_L;
    conf->pcie_slv_conf.pcie_G = DEFAULT_PCIE_SLV_G;

    return SPIN_SUCCESS;
}

int pspinsim_init(int argc, char **argv, pspin_conf_t *conf) 
{
    Verilated::commandArgs(argc, argv);
    Vpspin_verilator *tb = new Vpspin_verilator();
    sim = new SimControl<Vpspin_verilator>(tb, VCD_FILE);

    pspin_conf_t default_conf;
    if (conf==NULL) {
        pspinsim_default_conf(&default_conf);
        conf = &default_conf;
    }

    // Define ports
    AXI_MASTER_PORT_ASSIGN(tb, ni_slave, &ni_mst);
    NI_CTRL_PORT_ASSIGN(&fmq_input_port, her, &ni_control)    
    AXI_MASTER_PORT_ASSIGN(tb, no_slave, &no_mst);
    NO_CMD_PORT_ASSIGN(tb, nic_cmd, &no_cmd);
    AXI_SLAVE_PORT_ASSIGN(tb, host_master, &pcie_slv_port);
    AXI_MASTER_PORT_ASSIGN(tb, host_slave, &pcie_mst_port);
    TASK_CTRL_PORT_ASSIGN(tb, task, &sched_port);

    // Instantiate simulation-only modules
    ni = new NICInbound<AXIPort<uint32_t, uint64_t>>(ni_mst, ni_control, L2_PKT_BUFF_START, L2_PKT_BUFF_SIZE);
    no = new NICOutbound<AXIPort<uint32_t, uint64_t>>(no_mst, no_cmd, conf->no_conf.network_G, conf->no_conf.max_pkt_size, conf->no_conf.max_network_queue_len);
    pcie_slv = new PCIeSlave<AXIPort<uint64_t, uint64_t>>(pcie_slv_port, conf->pcie_slv_conf.axi_aw_buffer, conf->pcie_slv_conf.axi_w_buffer, conf->pcie_slv_conf.axi_ar_buffer, conf->pcie_slv_conf.axi_r_buffer, conf->pcie_slv_conf.axi_b_buffer, conf->pcie_slv_conf.pcie_L, conf->pcie_slv_conf.pcie_G);
    pcie_mst = new PCIeMaster<AXIPort<uint32_t, uint64_t>>(pcie_mst_port);
    fmq_eng = new FMQEngine(fmq_input_port, sched_port);

    // Add simulation only modules
    sim->add_module(*ni);
    sim->add_module(*no);
    sim->add_module(*pcie_slv);
    sim->add_module(*pcie_mst);
    sim->add_module(*fmq_eng);

    //before the reset!    
    const char *slm_files_path = conf->slm_files_path;
    if (slm_files_path==NULL) {
        char *pspin_hw_env = getenv("PSPIN_HW");
        if (pspin_hw_env == NULL) {
            printf("Error: you need to either specify where to read SLM files from or set PSPIN_HW env var and put slm files in sim_files/slm_files/!\n");
            return SPIN_ERR;
        }
        snprintf(slm_path, PATH_MAX, "%s/sim_files/slm_files/", pspin_hw_env);
    } else {
        snprintf(slm_path, PATH_MAX, "%s/", slm_files_path);
    }

    // Send reset signal
    sim->reset();

    return SPIN_SUCCESS;
}

int pspinsim_run()
{
    // Main loop
    sim->run_all();

    return SPIN_SUCCESS;
}

int pspinsim_run_tick(uint8_t* done_flag)
{
    // Single step of the main loop
    *done_flag = 0;
    sim->run_single();
    if (sim->done()) *done_flag = 1;

    return SPIN_SUCCESS;
}

int pspinsim_fini() 
{
    printf("\n###### Statistics ######\n");
    for (auto it = sim->get_modules().begin(); it != sim->get_modules().end(); ++it){
        it->get().print_stats();
        printf("----------------------------------\n");
    }
    delete sim;
    
    return SPIN_SUCCESS;
}

int pspinsim_packet_trace_read(const char* pkt_file_path, const char* data_file_path)
{
    return ni->read_trace(pkt_file_path, data_file_path);
}

int pspinsim_packet_add(spin_ec_t* ec, uint32_t msgid, uint8_t* pkt_data, size_t pkt_len, size_t pkt_l1_len, uint8_t eom, uint32_t wait_cycles, uint64_t user_ptr)
{
    her_descr_t her;
    memcpy(&(her.mpq_meta), ec, sizeof(spin_ec_t));

    her.msgid = msgid;
    her.eom = eom;
    her.her_addr = 0; //will be assigned later
    her.her_size = pkt_len;
    her.xfer_size = pkt_l1_len;
    her.user_ptr = user_ptr;

    return ni->add_packet(her, pkt_data, pkt_len, wait_cycles);
}

int pspinsim_packet_eos()
{
    ni->set_eos();
    return SPIN_SUCCESS;
}

int pspinsim_cb_set_pkt_out(pkt_out_cb_t cb)
{
    NICOutbound<AXIPort<uint32_t, uint64_t>>::out_packet_cb_t f(cb);   
    no->set_packet_out_cb(f);
    return SPIN_SUCCESS;
}


int pspinsim_cb_set_pcie_slv_write(pcie_slv_write_cb_t cb)
{
    PCIeSlave<AXIPort<uint64_t, uint64_t>>::slv_write_cb_t f(cb);
    pcie_slv->set_slv_write_cb(f);
    return SPIN_SUCCESS;
}


int pspinsim_cb_set_pcie_slv_read(pcie_slv_read_cb_t cb)
{
    PCIeSlave<AXIPort<uint64_t, uint64_t>>::slv_read_cb_t f(cb);
    pcie_slv->set_slv_read_cb(f);
    return SPIN_SUCCESS;
}

int pspinsim_cb_set_pcie_mst_write_completion(pcie_mst_write_cb_t cb)
{
    PCIeMaster<AXIPort<uint32_t, uint64_t>>::mst_write_cb_t f(cb);
    pcie_mst->set_mst_write_cb(f);
    return SPIN_SUCCESS;
}

int pspinsim_cb_set_pcie_mst_read_completion(pcie_mst_read_cb_t cb)
{
    PCIeMaster<AXIPort<uint32_t, uint64_t>>::mst_read_cb_t f(cb);
    pcie_mst->set_mst_read_cb(f);
    return SPIN_SUCCESS;
}

int pspinsim_cb_set_pkt_feedback(pkt_feedback_cb_t cb)
{
    NICInbound<AXIPort<uint32_t, uint64_t>>::pkt_feedback_cb_t f(cb);   
    ni->set_feedback_cb(f);
    return SPIN_SUCCESS;
}

/* sPIN API functions (these are inteded to be into the actual API, no simulation) */
int spin_nicmem_write(spin_nic_addr_t addr, void *data, size_t size, void* user_ptr)
{
    pcie_mst->nic_mem_write(addr, (uint8_t*) data, size, user_ptr);
    return SPIN_SUCCESS;
}

int spin_nicmem_read(spin_nic_addr_t addr, void *data, size_t size, void* user_ptr)
{
    pcie_mst->nic_mem_read(addr, (uint8_t*) data, size, user_ptr);
    return SPIN_SUCCESS;
}


// this will be swapped with Timo's stuff
int spin_find_handler_by_name(const char *binfile, const char* handler_name, spin_nic_addr_t *handler_addr, size_t *handler_size)
{
    struct stat sb;
    FILE *f = fopen(binfile, "rb");
    int fno = fileno(f);
    fstat(fno, &sb);

    Elf32_Ehdr *elf_ptr = (Elf32_Ehdr*) mmap(NULL, sb.st_size, PROT_READ, MAP_PRIVATE, fno, 0);
    uint32_t num_sections = elf_ptr->e_shnum;

    Elf32_Shdr *section_header_table = (Elf32_Shdr *)(((uint8_t *)elf_ptr) + elf_ptr->e_shoff);

    Elf32_Shdr *section_header_string_table = &(section_header_table[elf_ptr->e_shstrndx]);
    char *sec_string_table = (char *)(((uint8_t *)elf_ptr) + section_header_string_table->sh_offset);

    //find string table for the symbols
    char *sym_string_tab = NULL;
    for (int i = 0; i < num_sections; i++)
    {
        //printf("section: %s\n", sec_string_table + section_header_table[i].sh_name);
        char *sec_name = sec_string_table + section_header_table[i].sh_name;
        if (!strcmp(sec_name, ".strtab"))
        {
            sym_string_tab = (char *)(((uint8_t *)elf_ptr) + section_header_table[i].sh_offset);
        }
    }
    assert(sym_string_tab != NULL);

    for (int i = 0; i < num_sections; i++)
    {
        if (section_header_table[i].sh_type == SHT_SYMTAB)
        {
            //printf("sh type: %u; sh addr: %x\n", section_header_table[i].sh_type, section_header_table[i].sh_addr);

            Elf32_Sym *symbol_table = (Elf32_Sym *)(((uint8_t *)elf_ptr) + section_header_table[i].sh_offset);
            uint32_t num_symbols = section_header_table[i].sh_size / sizeof(Elf32_Sym);

            for (int j = 0; j < num_symbols; j++)
            {
                char *sym_name = sym_string_tab + symbol_table[j].st_name;

                if (!strcmp(sym_name, handler_name))
                {
                    *handler_addr = symbol_table[j].st_value;
                    *handler_size = 4096;
                    break;
                }
            }
        }
    }

    munmap(elf_ptr, sb.st_size);
    fclose(f);

    return SPIN_SUCCESS;
}
