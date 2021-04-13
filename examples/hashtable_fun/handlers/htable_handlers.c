#include <handler.h>

typedef void(*fun_ptr_t());

void fun1() __attribute__((used));
void fun2() __attribute__((used)); 
void fun3() __attribute__((used)); 

void fun1()
{
    printf("fun1!\n");
}

void fun2()
{
    printf("fun2!\n");
}

void fun3()
{
    printf("fun3!\n");
}


__handler__ void htable_hh(handler_args_t *args) {;}
__handler__ void htable_th(handler_args_t *args){;}


__handler__ void htable_ph(handler_args_t *args) 
{
    fun_ptr_t **htable = (fun_ptr_t**) args->task->handler_mem;

    //printf("payload handler (htable[1]: %p; fun2: %p)!\n", htable[1], fun2);

    //TODO: compute hash here and access entry accordingly!   
    (htable[0])();
    (htable[1])();
    (htable[2])();
    
}

void init_handlers(handler_fn * hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr)
{
    volatile handler_fn handlers[] = {htable_hh, htable_ph, htable_th};
    *hh = handlers[0];
    *ph = handlers[1];
    *th = handlers[2];
}
