/* Copyright 2020 ETH Zurich and University of Bologna. */
/* Solderpad Hardware License, Version 0.51, see LICENSE for details. */
/* SPDX-License-Identifier: SHL-0.51 */

OUTPUT_ARCH( "riscv" )
ENTRY(_start)

MEMORY
{
  prog_mem          : ORIGIN = 0x1e000000, LENGTH = 0x8000
  L2           		  : ORIGIN = 0x1c000000, LENGTH = 0x00300000
  L2_handler_data	  : ORIGIN = 0x1c000000, LENGTH = 0x00400000
  L1                : ORIGIN = 0x10000000, LENGTH = 0x00100000
  L1_aliased        : ORIGIN = 0x1b000000, LENGTH = 0x00100000
}

__l1_reserved = 0x400;
__rt_stack_size = 0x400;
__harts_per_cluster = 8;
__cluster_address_space = 0x400000;

SECTIONS
{
  .init :
  {
    *(.init)
  } > prog_mem

  .text :
  {
    . = ALIGN(4);
    _stext = .;
    *(.text)
    *(.text.*)
    _etext  =  .;
    *(.lit)
    *(.shdata)
    _endtext = .;
    . = ALIGN(4);
  } > prog_mem

  .stack : {
    . = ALIGN(4);
    . = ALIGN(16);
    . = . + __l1_reserved;
    stack = .;
  } > L1
}
