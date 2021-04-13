#include <hal/pulp.h>
#include "handler.h"
#include "util.h"
#include "pspin_rt.h"
#include "spin_dma.h"
#include "hwsched.h"


/** DMA functions **/

int spin_dma(void* source, void* dest, size_t size, int direction, int options, spin_dma_t* xfer)
{
    *xfer = spin__memcpy_nonblk(source, dest, (uint32_t)size);
    return SPIN_OK;
}

int spin_dma_wait(spin_dma_t xfer)
{
    spin__wait_for_tf_completion(xfer);
    return SPIN_OK;
}

int spin_dma_test(spin_dma_t xfer, uint32_t *completed)
{
    *completed = spin__tf_completed(xfer);
    return SPIN_OK;
}

/** Locks **/

int spin_lock_init(spin_lock_t* lock)
{
    futex_init(lock);
    return SPIN_OK;
}

int spin_lock_try_lock(spin_lock_t* lock)
{
    return futex_try_lock(lock);
}

int spin_lock_lock(spin_lock_t* lock)
{
    futex_lock_s(lock);
    return SPIN_OK;
}

int spin_lock_unlock(spin_lock_t* lock)
{
    futex_unlock(lock);
    return SPIN_OK;
}


int spin_rw_lock_r_lock(spin_rw_lock_t *rwlock)
{
    int32_t num_readers = amo_add(&(rwlock->num_readers), 1) + 1;
    if (num_readers == 1)
    {
        spin_lock_lock(&(rwlock->glock));
    }
    return SPIN_OK;
}

int spin_rw_lock_r_unlock(spin_rw_lock_t *rwlock)
{
    int32_t num_readers = amo_add(&(rwlock->num_readers), -1) - 1;
    if (num_readers == 0)
    {
        spin_lock_unlock(&(rwlock->glock));
    }
    return SPIN_OK;
}

int spin_rw_lock_w_lock(spin_rw_lock_t *rwlock)
{
    spin_lock_lock(&(rwlock->glock));
    return SPIN_OK;
}

int spin_rw_lock_w_unlock(spin_rw_lock_t *rwlock)
{
    spin_lock_unlock(&(rwlock->glock));
    return SPIN_OK;
}


/** NIC commands **/
int spin_cmd_wait(spin_cmd_t handle) 
{
    MMIO_WRITE(CMD_WAIT, handle);
    return SPIN_OK;
}

int spin_cmd_test(spin_cmd_t handle, bool *completed)
{
    MMIO_WRITE(CMD_TEST, handle);
    *completed = MMIO_READ(CMD_TEST) == 1;
    return SPIN_OK;
} 

int spin_rdma_put(uint32_t dest, void *data, uint32_t length, spin_cmd_t *handle)
{
    uint32_t fid = 1 /* >1 is RDMA */;
    uint32_t src_addr_high = 0;
    uint32_t cmd_info = 2;
    //length, src_addr_low, src_addr_high, fid, nid
    uint32_t res;
    uint32_t base_addr = 0x1b205000;
    asm volatile(" sw      %2, 168(%1);  \
                   sw      %3, 164(%1);  \
                   sw      %4, 160(%1);  \
                   sw      %5, 156(%1);  \
                   sw      %6, 152(%1);  \
                   sw      %7, 140(%1);  \
                   lw      %0, 128(%1);  \
    " : "=r"(res) : "r"(base_addr), "r"(dest), "r"(fid), "r"(src_addr_high), "r"((uint32_t)data), "r"(length), "r"(cmd_info));       
    
    *handle = res;
    return SPIN_OK;
}


int spin_send_packet(void *data, uint32_t length, spin_cmd_t *handle)
{
    uint32_t dest = 0;
    uint32_t fid = 0 /* fid is used as QP ID. fid=0 -> no QP, it's raw data */;
    uint32_t src_addr_high = 0;
    uint32_t cmd_info = 2;
    //length, src_addr_low, src_addr_high, fid, nid
    uint32_t res;
    uint32_t base_addr = 0x1b205000;
    asm volatile(" sw      %2, 168(%1);  \
                   sw      %3, 164(%1);  \
                   sw      %4, 160(%1);  \
                   sw      %5, 156(%1);  \
                   sw      %6, 152(%1);  \
                   sw      %7, 140(%1);  \
                   lw      %0, 128(%1);  \
    " : "=r"(res) : "r"(base_addr), "r"(dest), "r"(fid), "r"(src_addr_high), "r"((uint32_t)data), "r"(length), "r"(cmd_info));       
    
    *handle = res;
    return SPIN_OK;
}

int spin_host_write(uint64_t host_addr, uint64_t user_data, bool generate_event) 
{
    /* WARNING: HostDirect is not implemented yet. This method just prepares a dma_to_host command but does not issue it. */

    uint32_t host_address_high = (uint32_t) (host_addr >> 32);
    uint32_t host_address_low = (uint32_t) host_addr;

    uint32_t data_high = (uint32_t) (user_data >> 32);
    uint32_t data_low = (uint32_t) user_data;

    uint32_t direction = 1<<31; //NIC -> host
    uint32_t cmd_info = (uint8_t) generate_event;

    //length, src_addr_low, src_addr_high, fid, nid
    uint32_t res;
    uint32_t base_addr = 0x1b205000;
    asm volatile(" sw      %2, 168(%1);  \
                   sw      %3, 164(%1);  \
                   sw      %4, 160(%1);  \
                   sw      %5, 156(%1);  \
                   sw      %6, 144(%1);  \
                   sw      %7, 140(%1);  \
                   add     %0, %0, x0;  \
    " : "=r"(res) : "r"(base_addr), "r"(host_address_high), "r"(host_address_low), "r"(data_high), "r"(data_low), "r"(direction), "r"(cmd_info));       

    return SPIN_OK;
}


int spin_dma_to_host(uint64_t host_addr, uint32_t nic_addr, uint32_t length, bool generate_event, spin_cmd_t *xfer)
{
    uint32_t host_address_high = (uint32_t) (host_addr >> 32);
    uint32_t host_address_low = (uint32_t) host_addr;
    uint32_t direction = 1<<31; //NIC -> host
    uint32_t cmd_info = (uint8_t) generate_event;

    //length, src_addr_low, src_addr_high, fid, nid
    uint32_t res;
    uint32_t base_addr = 0x1b205000;
    asm volatile(" sw      %2, 168(%1);  \
                   sw      %3, 164(%1);  \
                   sw      %4, 160(%1);  \
                   sw      %5, 156(%1);  \
                   sw      %6, 144(%1);  \
                   sw      %7, 140(%1);  \
                   lw      %0, 128(%1);  \
    " : "=r"(res) : "r"(base_addr), "r"(host_address_high), "r"(host_address_low), "r"(nic_addr), "r"(length), "r"(direction), "r"(cmd_info));       
    
    *xfer = res;
    return SPIN_OK;
}

int spin_dma_from_host(uint64_t host_addr, uint32_t nic_addr, uint32_t length, bool generate_event, spin_cmd_t *xfer)
{
    uint32_t host_address_high = (uint32_t) (host_addr >> 32);
    uint32_t host_address_low = (uint32_t) host_addr;
    uint32_t direction = 0; //host -> NIC
    uint32_t cmd_info = (uint8_t) generate_event;

    //length, src_addr_low, src_addr_high, fid, nid
    uint32_t res;
    uint32_t base_addr = 0x1b205000;
    asm volatile(" sw      %2, 168(%1);  \
                   sw      %3, 164(%1);  \
                   sw      %4, 160(%1);  \
                   sw      %5, 156(%1);  \
                   sw      %6, 144(%1);  \
                   sw      %7, 140(%1);  \
                   lw      %0, 128(%1);  \
    " : "=r"(res) : "r"(base_addr), "r"(host_address_high), "r"(host_address_low), "r"(nic_addr), "r"(length), "r"(direction), "r"(cmd_info));       
    
    *xfer = res;
    return SPIN_OK;
}

