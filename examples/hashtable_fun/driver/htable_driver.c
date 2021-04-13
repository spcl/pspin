#include "pspinsim.h"
#include "spin.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#define NUM_FUNCTIONS 3

#define CHECK_ERR(S) {int res; if ((res=S)!=SPIN_SUCCESS) return res;}

#define NUM_PACKETS 32
#define PKT_SIZE 64

/* This is the handler data memory */
#define NIC_L2_ADDR 0x1c300000

#define HANDLERS_FILE "build/htable"

/*** Test function that injects some (empty) packets ***/
int send_packets()
{
    uint8_t pkt_buffer[PKT_SIZE];

    // find address of the payload handler
    spin_nic_addr_t ph_addr;
    size_t ph_size;
    CHECK_ERR(spin_find_handler_by_name(HANDLERS_FILE, "htable_ph", &ph_addr, &ph_size));

    /* 1st thing to do: prepare execution context */
    spin_ec_t ec;
    ec.handler_mem_addr = (uint32_t) NIC_L2_ADDR; 
    ec.handler_mem_size = 0x100000;
    ec.host_mem_addr    = (uint64_t) 0xdeadbeefdeadbeef;
    ec.host_mem_size    = 0;
    ec.hh_addr          = 0; //hh_addr;
    ec.ph_addr          = ph_addr;
    ec.th_addr          = 0; //th_addr;
    ec.hh_size          = 0;
    ec.ph_size          = ph_size;
    ec.th_size          = 0;
    
    for (int i=0; i<NUM_PACKETS; i++)
    {
        pspinsim_packet_add(&ec, 0, pkt_buffer, PKT_SIZE, PKT_SIZE, i == NUM_PACKETS - 1, 0);
    }

    // this tells the NIC inbound engine that we are not going to send any more packet
    pspinsim_packet_eos();

    return 0;
}

/*** Callbacks ***/
void pcie_mst_write_complete(void *user_ptr)
{
    printf("Write to NIC memory completed (user_ptr: %p)\n", user_ptr);

    // we can start sending packets as soon as the handler code is in memory
    send_packets();
}

/*** Main ***/
int main(int argc, char**argv)
{
    pspin_conf_t conf;
    pspinsim_default_conf(&conf);

    pspinsim_init(argc, argv, &conf);
    pspinsim_cb_set_pcie_mst_write_completion(pcie_mst_write_complete);


    /* Prepare NIC memory */
    // 1) find addresses of functions that we want to address
    spin_nic_addr_t fun_addr[NUM_FUNCTIONS];
    size_t fun_size[NUM_FUNCTIONS];
    CHECK_ERR(spin_find_handler_by_name(HANDLERS_FILE, "fun1", &(fun_addr[0]), &(fun_size[0])));
    CHECK_ERR(spin_find_handler_by_name(HANDLERS_FILE, "fun2", &(fun_addr[1]), &(fun_size[1])));
    CHECK_ERR(spin_find_handler_by_name(HANDLERS_FILE, "fun3", &(fun_addr[2]), &(fun_size[2])));

    printf("fun1: %x; fun2: %x; fun3: %x\n", fun_addr[0], fun_addr[1], fun_addr[2]);

    // 2) write the array (which is our hash table) to the NIC address
    spin_nicmem_write(NIC_L2_ADDR, (void*) fun_addr, sizeof(spin_nic_addr_t)*NUM_FUNCTIONS, (void*) 0xcafebebe);
    
    // 3) at this point we need to wait for the write to complete. We will be called back on "pcie_mst_write_complete" when completed.
    /* End NIC memory preparation */

    pspinsim_run();

    pspinsim_fini();

    return 0;
}