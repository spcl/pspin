/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * Authors: 
 *   Germain Haugou, ETH (germain.haugou@iis.ee.ethz.ch)
 *   Salvatore Di Girolamo, ETH (digirols@inf.ethz.ch)
 */

#include "archi/pulp.h"
#include "archi/eu/eu_v3.h"

  .section .text

_entry:
  # activate dispatch event
  li      t0, (1<<PULP_DISPATCH_EVENT)
  li      t1, ARCHI_EU_DEMUX_ADDR
  sw      t0, EU_CORE_MASK(t1)

  # clear the bss segment
  la      t0, _bss_start
  la      t1, _bss_end
1:
  sw      zero,0(t0)
  addi    t0, t0, 4
  bltu    t0, t1, 1b

  /* Stack initialization */
  la      x2, stack

  /* set the stack pointer */
  /* get cluster ID */
  csrr    t0, 0xf14
  srai    t1, t0, 0x5
  p.bclr  t1, t1, 25, 6
  li      t2, ARCHI_CLUSTER_SIZE
  mul     t1, t1, t2 
  add     x2, x2, t1

  /* get core ID */
  p.bclr  t1, t0, 26, 5
  la      t2, __rt_stack_size
  mul     t2, t1, t2
  add     x2, x2, t2

  bne     t1, x0, __rt_slave_start
  jal     x1, cluster_init

  li      s2, ARCHI_EU_DEMUX_ADDR
  addi    t3, x0, -1
  sw      t3, EU_DISPATCH_DEMUX_OFFSET + EU_DISPATCH_TEAM_CONFIG(s2)
  sw      x0, EU_DISPATCH_DEMUX_OFFSET + EU_DISPATCH_FIFO_ACCESS(s2)

  /* Jump to the HPU entry function */
  jal     x1, hpu_entry

  .global _init
  .global _fini
_init:
_fini:
  # These don't have to do anything since we use init_array/fini_array.
  ret

 __rt_slave_start:
  li      s2, ARCHI_EU_DEMUX_ADDR
  p.elw   t0, EU_DISPATCH_DEMUX_OFFSET + EU_DISPATCH_FIFO_ACCESS(s2)

  jal     x1, hpu_entry

.section .vectors, "ax"
.option norvc;

  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler
  j __rt_no_irq_handler


  .org 0x80
  .global _start
_start:
  jal x0, _entry


__rt_no_irq_handler:
  j __rt_no_irq_handler

