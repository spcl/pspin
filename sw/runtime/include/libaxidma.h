// Copyright (c) 2020 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Thomas Benz <tbenz@ethz.ch>

// AXI DMA library for the pulp cluster frontend 

#include <stdint.h>


// base address of the dma
typedef struct {
    uint32_t src_addr_low;
    uint32_t src_addr_high;
    uint32_t dst_addr_low;
    uint32_t dst_addr_high;
    uint32_t num_bytes;
    volatile uint32_t tf_id   __attribute__((aligned(8)));
    volatile uint32_t done_id __attribute__((aligned(8)));
    volatile uint32_t config  __attribute__((aligned(8)));
} axidma__dma_conf_t;

// launch simple 1D transfer (supporting 64 bit addresses)
static inline uint32_t axidma__launch_oned_64(
    axidma__dma_conf_t* axidma__dma_conf,
    void* src_addr_low,
    void* src_addr_high,
    void* dst_addr_low,
    void* dst_addr_high,
    uint32_t num_bytes 
) {

    // configure the dma
    axidma__dma_conf->src_addr_low  = (uint32_t)src_addr_low;
    axidma__dma_conf->src_addr_high = (uint32_t)src_addr_high;
    axidma__dma_conf->dst_addr_low  = (uint32_t)dst_addr_low;
    axidma__dma_conf->dst_addr_high = (uint32_t)dst_addr_high;
    axidma__dma_conf->num_bytes     = (uint32_t)num_bytes;

    __asm__ __volatile__ ("" : : : "memory");

    // launch the transfer
    return axidma__dma_conf->tf_id;
}


// launch simple 1D transfer
// make sure the high address registers are correctly set!
static inline uint32_t axidma__launch_oned( 
    axidma__dma_conf_t* axidma__dma_conf,
    void* src_addr,                                          
    void* dst_addr,
    uint32_t num_bytes  
) {

    // configure the dma
    axidma__dma_conf->src_addr_low  = (uint32_t)src_addr;
    axidma__dma_conf->dst_addr_low  = (uint32_t)dst_addr;
    axidma__dma_conf->num_bytes     = (uint32_t)num_bytes;

    __asm__ __volatile__ ("" : : : "memory");

    // launch the transfer
    return axidma__dma_conf->tf_id;
}


// use to set the the segment address in a segmented system
static inline void axidma__set_seg_addr( 
    axidma__dma_conf_t* axidma__dma_conf,
    void* src_seg_addr,
    void* dsc_seg_addr  
) {

    // configure the upper 64 bit addresses
    axidma__dma_conf->src_addr_high = (uint32_t)src_seg_addr;
    axidma__dma_conf->dst_addr_high = (uint32_t)dsc_seg_addr;

}


// clear upper address registers
static inline void axidma__clear_seg_addr(
    axidma__dma_conf_t* axidma__dma_conf
) {

    // clear both upper address registers
    axidma__set_seg_addr(axidma__dma_conf, 0, 0);
}


// read the id of the last transaction that has been completed
static inline uint32_t axidma__read_completed_id(
    axidma__dma_conf_t* axidma__dma_conf
) {

    return axidma__dma_conf->done_id;
}


// wait for a given transaction to complete
static inline void axidma__wait_for_tf_completion(
    axidma__dma_conf_t* axidma__dma_conf,
    uint32_t tf_id
) {

    // spin until transfer is completed
    while (tf_id > axidma__read_completed_id(axidma__dma_conf)) {
        asm volatile ("nop");
    }
}


// test if a given transaction has been completed
static inline char axidma__tf_completed(
    axidma__dma_conf_t* axidma__dma_conf,
    uint32_t tf_id
) {

    return (tf_id <= axidma__read_completed_id(axidma__dma_conf));
}


// non-blocking transfer
static inline uint32_t axidma__memcpy_nonblk( 
    axidma__dma_conf_t* axidma__dma_conf,
    void* src_addr,
    void* dst_addr,
    uint32_t num_bytes 
) {

    return axidma__launch_oned(axidma__dma_conf, src_addr, dst_addr, num_bytes);
}


// blocking transfer
static inline void axidma__memcpy(
    axidma__dma_conf_t* axidma__dma_conf,
    void* src_addr,       
    void* dst_addr,
    uint32_t num_bytes 
) {

    volatile uint32_t tf_id = axidma__launch_oned(axidma__dma_conf, src_addr, dst_addr, num_bytes);
    // spin until transfer is completed
    while (tf_id > axidma__read_completed_id(axidma__dma_conf)) {
        asm volatile ("nop");
    }
}
