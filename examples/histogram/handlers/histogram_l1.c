#ifndef HOST
#include <handler.h>
#else
#include <handler_profiler.h>
#endif

#include <packets.h>
#include <spin_conf.h>

#define NUM_CLUSTERS 4
#define STRIDE 1
#define OFFSET 0
#define NUM_INT_OP 0

#define HISTOGRAM_SIZE 1024

#ifndef HOST
typedef uint32_t pspin_mem_ptr_t;
volatile __attribute__((section(".l2_handler_data"))) uint8_t handler_mem[] = {0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x2, 0x0, 0x0};
#else
typedef uint64_t pspin_mem_ptr_t;
volatile __attribute__((section(".l2_handler_data"))) uint8_t handler_mem[] = {0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x2, 0x0, 0x0};
#endif

__handler__ void histogram_l1_hh(handler_args_t *args)
{
}


__handler__ void histogram_l1_ph(handler_args_t *args)
{
    task_t* task = args->task;
    
    uint8_t *pkt_pld_ptr;
    uint32_t pkt_pld_len;
    GET_IP_UDP_PLD(task->pkt_mem, pkt_pld_ptr, pkt_pld_len);
    pkt_pld_ptr += sizeof(app_hdr_t);
    pkt_pld_len -= sizeof(app_hdr_t);

    int32_t *nic_pld_addr = (int32_t*) pkt_pld_ptr;

    int32_t *local_mem = (int32_t*) (task->scratchpad[args->cluster_id]);
    //volatile uint8_t *local_mem = (volatile uint8_t*) (task->scratchpad[args->cluster_id]);
    //printf("pktpld: %p; pkt_pld_len: %lu\n", nic_pld_addr, pkt_pld_len);
    
    volatile int32_t* word_ptr = &(local_mem[nic_pld_addr[0]]);
    //int32_t mul = 4;
    //we assume the number of msg size divides the pkt payload size
    for (uint32_t i = 1; i < pkt_pld_len / 4; i++)
    {
        //amo_add(&(local_mem[nic_pld_addr[i]]), 1);
        
        //uint32_t word_idx = nic_pld_addr[i]; //FAST_MOD(nic_pld_addr[i], HISTOGRAM_SIZE);
        //word_ptr = (volatile int32_t*) local_mem;
        //asm volatile("p.mac %0, %1, %2" : : "r"(word_ptr),  "r"(nic_pld_addr[i]), "r"(mul));

        //word_ptr = (volatile int32_t*) (local_mem + (nic_pld_addr[i] << 2));
        //amo_add(word_ptr, 1); 

        amo_add(word_ptr, 1); 
        word_ptr = &(local_mem[nic_pld_addr[i]]);
    }
}
__handler__ void histogram_l1_th(handler_args_t *args)
{
    task_t* task = args->task;
    uint64_t host_address = task->host_mem_high;
    host_address = (host_address << 32) | (task->host_mem_low);

    //signal that we completed so to let the host read the result back
    spin_host_write(host_address, (uint64_t) 1, false);
}

void init_handlers(handler_fn *hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {histogram_l1_hh, histogram_l1_ph, histogram_l1_th};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];

    *handler_mem_ptr = (void *)handler_mem;
}
