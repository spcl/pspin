# Copyright 2020 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This file defines the `_start` symbol and initializes the global pointer. This
# is common among all bare runtimes.


# Expected from bootloader:
# - a0: mhartid
.section .init
_start:
  .globl _start
  
  // hard ID
  csrr    t0, 0xf14

  // get cluster ID
  srli    t1, t0, 16

  // get core ID 
  lui     t2, 16
  addi    t2, t2, -1
  and     t2, t0, t2

  // get stack base poitner (cluster-wide)
  la      x2, stack
  la      t0, __cluster_address_space
  mul     t0, t0, t1 
  add     x2, x2, t0

  // get hart stack pointer
  la      t0, __rt_stack_size
  mul     t0, t0, t2
  add     x2, x2, t0

  /* Jump to the HPU entry function */
  jal     x1, hpu_entry
