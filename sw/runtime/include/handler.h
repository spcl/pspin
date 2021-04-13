#pragma once

//#include "pulp.h"
#include "pspin.h"
#include "util.h"
#include "spin_conf.h"
#include "spin_dma.h"
#include "hwsched.h"

#define __handler__ __attribute__((used))

#define SPIN_DMA_EXT2LOC PLP_DMA_EXT2LOC
#define SPIN_DMA_LOC2EXT PLP_DMA_LOC2EXT
#define SPIN_OK 0x0
#define SPIN_FAIL 0x1


#define GET_IP_UDP_PLD(pkt_ptr, pkt_pld_ptr, pkt_pld_len)                           \
{                                                                                   \
    ip_hdr_t *ip_hdr = (ip_hdr_t*) (pkt_ptr);                                       \
    pkt_pld_len = ip_hdr->length - sizeof(ip_hdr_t) - sizeof(udp_hdr_t);            \
    pkt_pld_ptr = ((uint8_t *) pkt_ptr) + (ip_hdr->ihl * 4) + sizeof(udp_hdr_t);    \
}

typedef futex_t spin_lock_t;

typedef struct task 
{
    //handler memory (L2)
    void* handler_mem;
    size_t handler_mem_size;

    //packet memory (L1)
    void* pkt_mem;
    size_t pkt_mem_size;
    
    //per-message scratchpad (L1)
    void* scratchpad[NB_CLUSTERS];
    size_t scratchpad_size[NB_CLUSTERS];

    //host memory region
    uint32_t host_mem_high;
    uint32_t host_mem_low;
    size_t host_mem_size;

    //l2 pkt addr
    void* l2_pkt_mem;

    //home cluster id
    uint32_t home_cluster_id;

    //flow id
    uint32_t flow_id;

}__attribute__((__packed__)) task_t; 

typedef struct handler_args 
{
    task_t *task;
    uint32_t hpu_gid;
    uint32_t cluster_id;
    uint32_t hpu_id;
} handler_args_t;

typedef void (*handler_fn)(handler_args_t*);

typedef dma_t spin_dma_t;

typedef struct spin_rw_lock {
    spin_lock_t glock;
    volatile int32_t num_readers;
} spin_rw_lock_t;


static inline int spin_dma(void* source, void* dest, size_t size, int direction, int options, spin_dma_t* xfer)
{
    *xfer = spin__memcpy_nonblk(source, dest, (uint32_t)size);
    return SPIN_OK;
}

static inline int spin_dma_wait(spin_dma_t xfer)
{
    spin__wait_for_tf_completion(xfer);
    return SPIN_OK;
}

static inline int spin_dma_test(spin_dma_t xfer, uint32_t *completed)
{
    *completed = spin__tf_completed(xfer);
    return SPIN_OK;
}


/** Locks **/

static inline int spin_lock_init(spin_lock_t* lock)
{
    futex_init(lock);
    return SPIN_OK;
}

static inline int spin_lock_try_lock(spin_lock_t* lock)
{
    return futex_try_lock(lock);
}

static inline int spin_lock_lock(spin_lock_t* lock)
{
    futex_lock_s(lock);
    return SPIN_OK;
}

static inline int spin_lock_unlock(spin_lock_t* lock)
{
    futex_unlock(lock);
    return SPIN_OK;
}

static inline int spin_rw_lock_r_lock(spin_rw_lock_t *rwlock)
{
    int32_t num_readers = amo_add(&(rwlock->num_readers), 1) + 1;
    if (num_readers == 1)
    {
        spin_lock_lock(&(rwlock->glock));
    }
    return SPIN_OK;
}

static inline int spin_rw_lock_r_unlock(spin_rw_lock_t *rwlock)
{
    int32_t num_readers = amo_add(&(rwlock->num_readers), -1) - 1;
    if (num_readers == 0)
    {
        spin_lock_unlock(&(rwlock->glock));
    }
    return SPIN_OK;
}

static inline int spin_rw_lock_w_lock(spin_rw_lock_t *rwlock)
{
    spin_lock_lock(&(rwlock->glock));
    return SPIN_OK;
}

static inline int spin_rw_lock_w_unlock(spin_rw_lock_t *rwlock)
{
    spin_lock_unlock(&(rwlock->glock));
    return SPIN_OK;
}


typedef uint32_t spin_cmd_t;
static inline int spin_cmd_wait(spin_cmd_t handle) 
{
    MMIO_WRITE(CMD_WAIT, handle);
    return SPIN_OK;
}

static inline int spin_cmd_test(spin_cmd_t handle, bool *completed)
{
    MMIO_WRITE(CMD_TEST, handle);
    *completed = MMIO_READ(CMD_TEST) == 1;
    return SPIN_OK;
} 

static inline int spin_rdma_put(uint32_t dest, void *data, uint32_t length, spin_cmd_t *handle)
{
    uint32_t fid = 1 /* >1 is RDMA */;
    uint32_t src_addr_high = 0;
    uint32_t cmd_info = 2;
    //length, src_addr_low, src_addr_high, fid, nid
    uint32_t res;
    uint32_t base_addr = 0x1b205000;
    asm volatile(" sw      %2, 144(%1);  \
                   sw      %3, 148(%1);  \
                   sw      %5, 152(%1);  \
                   sw      %4, 156(%1);  \
                   sw      %6, 160(%1);  \
                   sw      %7, 140(%1);  \
                   lw      %0, 128(%1);  \
    " : "=r"(res) : "r"(base_addr), "r"(dest), "r"(fid), "r"(src_addr_high), "r"((uint32_t)data), "r"(length), "r"(cmd_info));       
    
    *handle = res;
    return SPIN_OK;
}

static inline int spin_send_packet(void *data, uint32_t length, spin_cmd_t *handle)
{
    uint32_t dest = 0;
    uint32_t fid = 0 /* fid is used as QP ID. fid=0 -> no QP, it's raw data */;
    uint32_t src_addr_high = 0;
    uint32_t cmd_info = 2;
    //length, src_addr_low, src_addr_high, fid, nid
    uint32_t res;
    uint32_t base_addr = 0x1b205000;
    asm volatile(" sw      %2, 144(%1);  \
                   sw      %3, 148(%1);  \
                   sw      %5, 152(%1);  \
                   sw      %4, 156(%1);  \
                   sw      %6, 160(%1);  \
                   sw      %7, 140(%1);  \
                   lw      %0, 128(%1);  \
    " : "=r"(res) : "r"(base_addr), "r"(dest), "r"(fid), "r"(src_addr_high), "r"((uint32_t)data), "r"(length), "r"(cmd_info));       
    
    *handle = res;
    return SPIN_OK;
}

static inline int spin_dma_to_host(uint64_t host_addr, uint32_t nic_addr, uint32_t length, bool generate_event, spin_cmd_t *xfer)
{
    uint32_t host_address_high = (uint32_t) (host_addr >> 32);
    uint32_t host_address_low = (uint32_t) host_addr;
    uint32_t direction = 1; //NIC -> host
    uint32_t cmd_info = (uint8_t) generate_event;

    //length, src_addr_low, src_addr_high, fid, nid
    uint32_t res;
    uint32_t base_addr = 0x1b205000;
    asm volatile(" sw      %2, 148(%1);  \
                   sw      %3, 144(%1);  \
                   sw      %4, 152(%1);  \
                   sw      %5, 156(%1);  \
                   sw      %6, 160(%1);  \
                   sw      %7, 140(%1);  \
                   lw      %0, 128(%1);  \
    " : "=r"(res) : "r"(base_addr), "r"(host_address_high), "r"(host_address_low), "r"(nic_addr), "r"(length), "r"(direction), "r"(cmd_info));       
    
    *xfer = res;
    return SPIN_OK;
}

static inline int spin_dma_from_host(uint64_t host_addr, uint32_t nic_addr, uint32_t length, bool generate_event, spin_cmd_t *xfer)
{
    uint32_t host_address_high = (uint32_t) (host_addr >> 32);
    uint32_t host_address_low = (uint32_t) host_addr;
    uint32_t direction = 0; //host -> NIC
    uint32_t cmd_info = (uint8_t) generate_event;

    //length, src_addr_low, src_addr_high, fid, nid
    uint32_t res;
    uint32_t base_addr = 0x1b205000;
    asm volatile(" sw      %2, 148(%1);  \
                   sw      %3, 144(%1);  \
                   sw      %4, 152(%1);  \
                   sw      %5, 156(%1);  \
                   sw      %6, 160(%1);  \
                   sw      %7, 140(%1);  \
                   lw      %0, 128(%1);  \
    " : "=r"(res) : "r"(base_addr), "r"(host_address_high), "r"(host_address_low), "r"(nic_addr), "r"(length), "r"(direction), "r"(cmd_info));       
    
    *xfer = res;
    return SPIN_OK;
}

// spin_host_write is deprecated. Use spin_write_to_host instead! 
#define spin_host_write spin_write_to_host

static inline int spin_write_to_host(uint64_t host_addr, uint64_t user_data, spin_cmd_t *xfer) 
{
    uint32_t host_address_high = (uint32_t) (host_addr >> 32);
    uint32_t host_address_low = (uint32_t) host_addr;

    uint32_t data_high = (uint32_t) (user_data >> 32);
    uint32_t data_low = (uint32_t) user_data;

    uint32_t size_and_direction = (0x8 << 1) | 0x1; // 8 bytes NIC -> host
    uint32_t cmd_info = (uint8_t) 4;

    uint32_t res;
    uint32_t base_addr = 0x1b205000;
    asm volatile(" sw      %2, 148(%1);  \
                   sw      %3, 144(%1);  \
                   sw      %4, 152(%1);  \
                   sw      %6, 156(%1);  \
                   sw      %5, 160(%1);  \
                   sw      %7, 140(%1);  \
                   lw      %0, 128(%1);  \
    " : "=r"(res) : "r"(base_addr), "r"(host_address_high), "r"(host_address_low), "r"(size_and_direction), "r"(data_high), "r"(data_low), "r"(cmd_info));       

    *xfer = res;
    return SPIN_OK;
}

//this function is only needed to avoid the compiler stripping away the handler functions (we don't reference them
//from the code but have pointers to them in the ME)
void init_handlers(handler_fn * hh, handler_fn *ph, handler_fn *th, void **handler_mem_ptr);
