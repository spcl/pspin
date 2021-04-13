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

// AXI DMA library for the spinningpulp soc

#include "libaxidma.h"

// cluster address ofsets
#define CLUSTER_BASE 0x10000000
#define DMA_OFFSET 0x1800

#define PRIVATE_DMA_BASE ARCHI_DEMUX_PERIPHERALS_ADDR + ARCHI_MCHAN_DEMUX_OFFSET
#define PUPLIC_DMA_BASE  CLUSTER_BASE + ARCHI_CLUSTER_PERIPHERALS_OFFSET + DMA_OFFSET


// non-blocking private transfer
static inline uint32_t spin__memcpy_nonblk( 
    void* src_addr,
    void* dst_addr,
    uint32_t num_bytes 
) {

	axidma__dma_conf_t* dma = (axidma__dma_conf_t* )(PRIVATE_DMA_BASE);
	return axidma__memcpy_nonblk(dma, src_addr, dst_addr, num_bytes);
}


// blocking private transfer
static inline void spin__memcpy(
    void* src_addr,       
    void* dst_addr,
    uint32_t num_bytes 
) {

	axidma__dma_conf_t* dma = (axidma__dma_conf_t* )(PRIVATE_DMA_BASE);
	axidma__memcpy(dma, src_addr, dst_addr, num_bytes);
}


// wait for a given private transaction to complete
static inline void spin__wait_for_tf_completion(
    uint32_t tf_id
) {

    // spin until transfer is completed
    axidma__dma_conf_t* dma = (axidma__dma_conf_t* )(PRIVATE_DMA_BASE);
    while (tf_id > axidma__read_completed_id(dma)) {
        asm volatile ("nop");
    }
}


// test if a given private transaction has been completed
static inline char spin__tf_completed(
    uint32_t tf_id
) {

	axidma__dma_conf_t* dma = (axidma__dma_conf_t* )(PRIVATE_DMA_BASE);
    return (tf_id <= axidma__read_completed_id(dma));
}


// non-blocking public transfer
static inline uint32_t spin__public_memcpy_nonblk( 
    void* src_addr,
    void* dst_addr,
    uint32_t num_bytes,
    uint32_t cluster_id
) {

	axidma__dma_conf_t* dma = (axidma__dma_conf_t* )(PUPLIC_DMA_BASE + cluster_id * ARCHI_CLUSTER_SIZE);
	return axidma__memcpy_nonblk(dma, src_addr, dst_addr, num_bytes);
}


// blocking public transfer
static inline void spin__public_memcpy(
    void* src_addr,       
    void* dst_addr,
    uint32_t num_bytes,
    uint32_t cluster_id
) {

	axidma__dma_conf_t* dma = (axidma__dma_conf_t* )(PUPLIC_DMA_BASE + cluster_id * ARCHI_CLUSTER_SIZE);
	axidma__memcpy(dma, src_addr, dst_addr, num_bytes);
}
	

// wait for a given private transaction to complete
static inline void spin__public_wait_for_tf_completion(
    uint32_t tf_id,
    uint32_t cluster_id
) {

    // spin until transfer is completed
    axidma__dma_conf_t* dma = (axidma__dma_conf_t* )(PUPLIC_DMA_BASE + cluster_id * ARCHI_CLUSTER_SIZE);
    while (tf_id > axidma__read_completed_id(dma)) {
        asm volatile ("nop");
    }
}


// test if a given private transaction has been completed
static inline char spin__public_tf_completed(
    uint32_t tf_id,
    uint32_t cluster_id
) {

	axidma__dma_conf_t* dma = (axidma__dma_conf_t* )(PUPLIC_DMA_BASE + cluster_id * ARCHI_CLUSTER_SIZE);
    return (tf_id <= axidma__read_completed_id(dma));
}
