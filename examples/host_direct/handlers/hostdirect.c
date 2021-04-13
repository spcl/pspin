
#include <handler.h>
#include <packets.h>
#include <spin_dma.h>


volatile __attribute__((section(".l2_handler_data"))) uint8_t handler_mem[] = {0xde, 0xad, 0xbe, 0xef};

__handler__ void hostdirect_hh(handler_args_t *args) {;}
__handler__ void hostdirect_ph(handler_args_t *args) 
{
    spin_cmd_t xfer;
    spin_host_write(0xdeadbeef, 0xcafebebe, &xfer);
}
__handler__ void hostdirect_th(handler_args_t *args){;}

void init_handlers(handler_fn * hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {hostdirect_hh, hostdirect_ph, hostdirect_th};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];

    *handler_mem_ptr = (void*) handler_mem;
}

