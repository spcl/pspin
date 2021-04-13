
#ifndef HOST
#include <handler.h>
#include <packets.h>
#include <spin_dma.h>
#else
#include <handler_profiler.h>
#endif

#ifndef NUM_INT_OP
#define NUM_INT_OP 0
#endif

volatile __attribute__((section(".l2_handler_data"))) uint8_t handler_mem[] = {0xde, 0xad, 0xbe, 0xef};

__handler__ void empty_hh(handler_args_t *args) {;}
__handler__ void empty_ph(handler_args_t *args) 
{
    //printf("Payload handler!\n");
#if (NUM_INT_OP > 0)
    volatile int xx = 0;
    int x = xx;
    for (int i=0; i<NUM_INT_OP; i++) {
        x = x*i;
    }
    xx = x;
#endif
}
__handler__ void empty_th(handler_args_t *args){;}

void init_handlers(handler_fn * hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {empty_hh, empty_ph, empty_th};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];

    *handler_mem_ptr = (void*) handler_mem;
}

