
OUTPUT_ARCH(riscv)
ENTRY( _start )

MEMORY
{
  prog_mem          : ORIGIN = 0x1d000000, LENGTH = 0x8000
  L2           		: ORIGIN = 0x1c000000, LENGTH = 0x00300000
  L2_handler_data	: ORIGIN = 0x1c300000, LENGTH = 0x00100000
  L2_queue     		: ORIGIN = 0x1c400000, LENGTH = 0x00400000
  L1                 	: ORIGIN = 0x10000000, LENGTH = 0x00100000
  L1_aliased         	: ORIGIN = 0x1b000000, LENGTH = 0x00100000
}

__ZERO = DEFINED(__ZERO) ? __ZERO  : 0;
__USE_UART = DEFINED(__USE_UART) ? __USE_UART : 0;
__RT_DEBUG_CONFIG = DEFINED(__RT_DEBUG_CONFIG) ? __RT_DEBUG_CONFIG   : (0 << 8) | 0;
__FC = DEFINED(__FC) ? __FC   : 1;
__L2 = DEFINED(__L2) ? __L2   : 0x80000;
__L1Cl = DEFINED(__L1Cl) ? __L1Cl : 0x10000;
__FETCH_ALL = DEFINED(__FETCH_ALL) ? __FETCH_ALL : 0x0;
__ACTIVE_FC = DEFINED(__ACTIVE_FC) ? __ACTIVE_FC : 0x1;
__rt_stack_size = DEFINED(__rt_stack_size) ? __rt_stack_size : 0x400;
__NB_ACTIVE_PE = DEFINED(__NB_ACTIVE_PE) ? __NB_ACTIVE_PE : 8;
__rt_platform = DEFINED(__rt_platform) ? __rt_platform : 3;
__rt_iodev = DEFINED(__rt_iodev) ? __rt_iodev : 0;
__rt_iodev_uart_value = DEFINED(__rt_iodev_uart_value) ? __rt_iodev_uart_value : 1;
__rt_iodev_uart_channel = DEFINED(__rt_iodev_uart_channel) ? __rt_iodev_uart_channel : 0;
__rt_iodev_uart_baudrate = DEFINED(__rt_iodev_uart_baudrate) ? __rt_iodev_uart_baudrate : 625000;
__rt_iodev_default_value = DEFINED(__rt_iodev_default_value) ? __rt_iodev_default_value : 0;
__rt_nb_cluster = DEFINED(__rt_nb_cluster) ? __rt_nb_cluster : 1;
__rt_nb_pe = DEFINED(__rt_nb_pe) ? __rt_nb_pe : 8;
__rt_cl_master_stack_size = DEFINED(__rt_cl_master_stack_size) ? __rt_cl_master_stack_size : 0x400;
__rt_cl_slave_stack_size = DEFINED(__rt_cl_slave_stack_size) ? __rt_cl_slave_stack_size : 0x400;
__rt_config = DEFINED(__rt_config) ? __rt_config : 0x1;
__rt_debug_init_config = DEFINED(__rt_debug_init_config) ? __rt_debug_init_config : 0x3;
__rt_debug_init_config_trace = DEFINED(__rt_debug_init_config_trace) ? __rt_debug_init_config_trace : 0x0;


/*
 * This linker script try to put FC data in L2 private bank0 and FC code 
 * in L2 private bank1 to avoid contention between FC code and data
 * as FC has no instruction cache and is so often accessing L2 to
 * get instructions. Everything can be shifted in case one bank is full.
 *
 * Cluster code and initialized data are put in shared banks to not polute
 * private banks which are quite small, and also avoid contentions between
 * cluster cache refill and FC.
 */


SECTIONS
{
  .vectors :
  {
    __irq_vector_base = .;
    KEEP(*(.vectors))
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

  .text.cluster :
  {
    __cluster_text_start = .;
    *(.cluster.text)
    *(.cluster.text.*)
    __cluster_text_end = .;
    . = ALIGN(4);
  } > prog_mem


  .rodata : {
    . = ALIGN(4);
    *(.rodata);
    *(.rodata.*)
    *(.srodata);
    *(.srodata.*)
    *(.eh_frame*)
  } > L2

  .data : {
    . = ALIGN(4);
    sdata  =  .;
    _sdata  =  .;
    *(.data);
    *(.data.*)
    *(.sdata);
    *(.sdata.*)
    *(.heapl2ram)
    . = ALIGN(4);
    edata  =  .;
    _edata  =  .;
  } > L2

  .bss : {
    . = ALIGN(8);
    _bss_start = .;
    *(.bss)
    *(.bss.*)
    *(.sbss)
    *(.sbss.*)
    *(COMMON)
    . = ALIGN(4);
    _bss_end = .;
  } > L2

  .l2_data : {
    . = ALIGN(4);
    *(.l2_data)
    *(.l2_data.*)
    *(.data_fc_shared)
    *(.data_fc_shared.*)
    . = ALIGN(4);
  } > L2

  __l2_data_end = ALIGN(8);

  __cluster_text_size = __cluster_text_end - __cluster_text_start;

  __l2_heap_start = ALIGN(4);

  __l2_heap_size = LENGTH(L2) - __l2_heap_start + ORIGIN(L2);


  /* Following sections are keeping the cluster data
   * in L2 until the cluster is powered up */

  _l1_preload_start_inL2 = ALIGN(4);

  .data_tiny_l1 :
  {
    . = ALIGN(4);
    _l1_preload_start = .;
    *(.data_tiny_l1)
    *(.data_tiny_l1.*)
    *(.data_alias_l1)
    *(.data_alias_l1.*)
  } > L1_aliased

  .stack : {
    . = ALIGN(4);
    . = ALIGN(16);
    . = . + 0x400;
    stack = .;
  } > L1


  _l1_preload_size = SIZEOF(.data_tiny_l1);

  .l2_handler_data : {
    . = ALIGN(4);
    KEEP(*(.l2_handler_data))
  } > L2_handler_data

  .l2_queue : {
    . = ALIGN(4);
  } > L2_queue
}

