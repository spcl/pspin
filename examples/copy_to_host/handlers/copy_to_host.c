#ifndef HOST
#include <handler.h>
#include <packets.h>
#include <spin_dma.h>
#else
#include <handler_profiler.h>
#endif

#if !defined(FROM_L2) && !defined(FROM_L1)
#define FROM_L1
#endif

volatile __attribute__((section(".l2_handler_data"))) uint8_t handler_mem[] = {0xde, 0xad, 0xbe, 0xef};


__handler__ void copy_to_host_hh(handler_args_t *args) {;}
__handler__ void copy_to_host_ph(handler_args_t *args)
{
    task_t* task = args->task;
    ip_hdr_t *ip_hdr = (ip_hdr_t*) (task->pkt_mem);
#ifdef FROM_L2
    uint8_t *nic_pld_addr = ((uint8_t*) (task->l2_pkt_mem)); 
#else
    uint8_t *nic_pld_addr = ((uint8_t*) (task->pkt_mem)); 
#endif
    uint16_t pkt_pld_len = ip_hdr->length;

    spin_cmd_t dma;

    uint64_t host_address = task->host_mem_high;
    host_address = (host_address << 32) | (task->host_mem_low);
    spin_dma_to_host(host_address, (uint32_t) nic_pld_addr, pkt_pld_len, 1, &dma);

    //It's not strictly necessary to wait. The hw will enforce that the feedback is not
    //sent until all commands issued by this handlers are completed.
#ifdef WAIT_POLL
    bool completed = false;
    do {
        spin_cmd_test(dma, &completed);
    } while (!completed);
#elif defined(WAIT_SUSPEND)
    spin_cmd_wait(dma);
#endif

}
__handler__ void copy_to_host_th(handler_args_t *args){;}

void init_handlers(handler_fn * hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {copy_to_host_hh, copy_to_host_ph, copy_to_host_th};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];

    *handler_mem_ptr = (void*) handler_mem;
}
