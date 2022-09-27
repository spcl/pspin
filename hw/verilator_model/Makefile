PSPIN_VERSION ?= undef
VERILATOR_CMD ?= verilator
VERILATOR_CC=$(VERILATOR_BIN)$(VERILATOR_CMD)
TOP_MODULE=pspin_verilator
SIM_LIB_SRCS=src/pspinsim.cpp

CXX ?= g++
VERILATOR_COMPILER_WORKERS ?= 8

TRACE_DEPTH?=6
VFLAGS_RELEASE=--Mdir obj_dir_release --sv -Wno-COMBDLY -Wno-UNOPTFLAT -Wno-NOLATCH -Wno-WIDTHCONCAT -j $(VERILATOR_COMPILER_WORKERS) +systemverilogext+sv -Wno-lint -CFLAGS "-fPIC"
VFLAGS_DEBUG=--Mdir obj_dir_debug --sv --assert --trace --trace-structs --trace-depth $(TRACE_DEPTH) -CFLAGS "-DVERILATOR_HAS_TRACE -fPIC" -Wno-COMBDLY -Wno-UNOPTFLAT -Wno-NOLATCH -Wno-WIDTHCONCAT -j $(VERILATOR_COMPILER_WORKERS) +systemverilogext+sv -Wno-lint


LIB_RELEASE_FLAGS=-fPIC --std=c++11 -Os -shared -Iobj_dir_release -I$(VERILATOR_ROOT)/include -I$(VERILATOR_ROOT)/include/vltstd/ -Iinclude/ 
LIB_DEBUG_FLAGS=-fPIC -g --std=c++11 -Os -shared -Iobj_dir_debug -I$(VERILATOR_ROOT)/include -I$(VERILATOR_ROOT)/include/vltstd/ -Iinclude/ -DVERILATOR_HAS_TRACE

EXE_RELEASE_FLAGS=-Iinclude/
EXE_DEBUG_FLAGS=-Iinclude/ -DVERILATOR_HAS_TRACE

SV_INC=-I../deps/axi/include/ -I../deps/common_cells/include -I../deps/cluster_interconnect/rtl/low_latency_interco/ -I../deps/riscv/include/
SV_SRCS=../deps/axi/src/axi_pkg.sv \
        ../deps/axi/src/axi_intf.sv \
        ../src/pulp_cluster_cfg_pkg.sv \
        ../src/pspin_cfg_pkg.sv \
        ../deps/cluster_interconnect/rtl/tcdm_interconnect/tcdm_interconnect_pkg.sv \
        ../deps/common_cells/src/fifo_v3.sv \
        ../deps/common_cells/src/stream_fifo.sv \
        ../deps/axi/src/axi_buf.sv \
        ../deps/common_cells/src/delta_counter.sv \
        ../deps/common_cells/src/cf_math_pkg.sv \
        ../deps/common_cells/src/lzc.sv \
        ../deps/common_cells/src/rr_arb_tree.sv \
        ../deps/common_cells/src/spill_register.sv \
        ../deps/axi/src/axi_demux.sv \
        ../deps/riscv/include/fpnew_pkg.sv \
        ../deps/riscv/include/riscv_defines.sv \
        ../deps/common_cells/src/deprecated/fifo_v2.sv \
        ../deps/common_cells/src/fall_through_register.sv \
        ../deps/common_cells/src/stream_demux.sv \
        ../deps/common_cells/src/stream_mux.sv \
        ../deps/common_cells/src/stream_fork.sv \
        ../deps/common_cells/src/stream_fork_dynamic.sv \
        ../deps/common_cells/src/stream_to_mem.sv \
        ../deps/common_cells/src/stream_join.sv \
        ../deps/axi2mem/src/axi_to_mem.sv \
        ../deps/cluster_interconnect/rtl/tcdm_interconnect/addr_dec_resp_mux.sv \
        ../deps/cluster_interconnect/rtl/tcdm_interconnect/xbar.sv \
        ../deps/cluster_interconnect/rtl/tcdm_interconnect/tcdm_interconnect.sv \
        ../deps/axi2mem/src/axi_to_mem_banked_mp.sv \
        ../deps/tech_cells_generic/src/rtl/tc_sram.sv \
        ../src/memories/sram.sv \
        ../src/memories/l2_mem.sv \
        ../src/pkt_scheduler/fifo_engine.sv \
        ../src/pkt_scheduler/mpq_engine.sv \
        ../src/pkt_scheduler/scheduler.sv \
        ../deps/axi/src/dma/axi_dma_burst_reshaper.sv \
        ../deps/axi/src/dma/axi_dma_data_path \
        ../deps/axi/src/dma/axi_dma_data_mover.sv \
        ../deps/axi/src/dma/axi_dma_backend.sv \
        ../deps/common_cells/src/addr_decode.sv \
        ../deps/common_cells/src/stream_register.sv \
        ../deps/common_cells/src/counter.sv \
        ../deps/axi/src/axi_atop_filter.sv \
        ../deps/axi/src/axi_err_slv.sv \
        ../deps/axi/src/axi_id_prepend.sv \
        ../deps/axi/src/axi_mux.sv \
        ../deps/axi/src/axi_xbar.sv \
        ../deps/axi/src/dma/frontends/pspin_soc_frontend/src/pspin_soc_dma.sv \
        ../src/soc_dma_wrap.sv \
        ../src/cmds/cmd_unit.sv \
        ../deps/pulp_cluster/packages/pulp_cluster_package.sv \
        ../deps/riscv/include/apu_core_package.sv \
        ../deps/pulp_cluster/packages/apu_package.sv \
        ../deps/cluster_interconnect/rtl/interfaces/xbar_tcdm_bus.sv \
        ../deps/cluster_interconnect/rtl/interfaces/xbar_periph_bus.sv \
        ../deps/pulp_cluster/rtl/cpu_marx_if.sv \
        ../deps/cluster_interconnect/rtl/interfaces/tcdm_bank_mem_bus.sv \
        ../deps/cluster_interconnect/rtl/interfaces/wide_dma_tcdm.sv \
        ../deps/cluster_peripherals/icache_ctrl_unit/interfaces/mp_pf_icache_ctrl_unit_bus.sv \
        ../deps/common_cells/src/rstgen_bypass.sv \
        ../deps/common_cells/src/rstgen.sv \
        ../deps/pulp_cluster/rtl/cluster_bus_wrap.sv \
        ../deps/axi_slice/src/axi_w_buffer.sv \
        ../deps/axi_slice/src/axi_r_buffer.sv \
        ../deps/axi_slice/src/axi_ar_buffer.sv \
        ../deps/axi_slice/src/axi_b_buffer.sv \
        ../deps/common_cells/src/deprecated/fifo_v1.sv \
        ../deps/axi_slice/src/axi_single_slice.sv \
        ../deps/axi_slice/src/axi_aw_buffer.sv \
        ../deps/axi2per/axi2per_req_channel.sv \
        ../deps/axi2per/axi2per_res_channel.sv \
        ../deps/axi2per/axi2per.sv \
        ../deps/pulp_cluster/rtl/axi2per_wrap.sv \
        ../deps/pulp_cluster/rtl/per_demux_wrap.sv \
        ../deps/per2axi/src/per2axi_req_channel.sv \
        ../deps/per2axi/src/per2axi_res_channel.sv \
        ../deps/per2axi/src/per2axi_busy_unit.sv \
        ../deps/per2axi/src/per2axi.sv \
        ../deps/pulp_cluster/rtl/per2axi_wrap.sv \
        ../deps/pulp_cluster/rtl/tryx_ctrl.sv \
        ../deps/cluster_interconnect/rtl/tcdm_interconnect/superbank_addr_decoder.sv \
        ../deps/cluster_interconnect/rtl/tcdm_interconnect/tcdm_superbank_mux.sv \
        ../deps/cluster_interconnect/rtl/tcdm_interconnect/amo_shim.sv \
        ../deps/cluster_interconnect/rtl/peripheral_interco/FanInPrimitive_Req_PE.sv \
        ../deps/cluster_interconnect/rtl/peripheral_interco/RR_Flag_Req_PE \
        ../deps/cluster_interconnect/rtl/peripheral_interco/ArbitrationTree_PE.sv \
        ../deps/cluster_interconnect/rtl/peripheral_interco/MUX2_REQ_PE.sv \
        ../deps/cluster_interconnect/rtl/peripheral_interco/AddressDecoder_Resp_PE.sv \
        ../deps/cluster_interconnect/rtl/peripheral_interco/RequestBlock2CH_PE.sv \
        ../deps/cluster_interconnect/rtl/peripheral_interco/FanInPrimitive_PE_Resp \
        ../deps/cluster_interconnect/rtl/peripheral_interco/ResponseTree_PE.sv \
        ../deps/cluster_interconnect/rtl/peripheral_interco/AddressDecoder_PE_Req.sv \
        ../deps/cluster_interconnect/rtl/peripheral_interco/ResponseBlock_PE.sv \
        ../deps/cluster_interconnect/rtl/peripheral_interco/XBAR_PE.sv \
        ../deps/pulp_cluster/rtl/cluster_interconnect_wrap.sv \
        ../deps/axi/src/axi_serializer.sv \
        ../deps/axi/src/dma/frontends/pulp_cluster_frontend/src/transfer_id_gen.sv \
        ../deps/axi/src/dma/frontends/pulp_cluster_frontend/src/pulp_cluster_frontend_regs.sv \
        ../deps/axi/src/dma/frontends/pulp_cluster_frontend/src/pulp_cluster_frontend.sv \
        ../deps/pulp_cluster/rtl/dmac_wrap.sv \
		../deps/axi2mem/src/axi_to_mem_interleaved.sv \
        ../deps/pulp_cluster/rtl/nhi_port_wrap.sv \
        ../deps/event_unit_flex/message_bus.sv \
        ../deps/cluster_peripherals/cluster_control_unit/cluster_control_unit.sv \
        ../deps/pulp_cluster/rtl/cluster_timer_wrap.sv \
        ../deps/timer_unit/rtl/timer_unit_counter_presc.sv \
        ../deps/timer_unit/rtl/timer_unit_counter.sv \
        ../deps/timer_unit/rtl/timer_unit.sv \
        ../deps/event_unit_flex/event_unit_interface_mux.sv \
        ../deps/pulp_cluster/rtl/cluster_event_map.sv \
        ../deps/event_unit_flex/interc_sw_evt_trig.sv \
        ../deps/event_unit_flex/event_unit_core.sv \
        ../deps/event_unit_flex/hw_barrier_unit.sv \
        ../deps/event_unit_flex/hw_mutex_unit.sv \
        ../deps/event_unit_flex/hw_dispatch.sv \
        ../deps/event_unit_flex/event_unit_top.sv \
        ../deps/cluster_peripherals/icache_ctrl_unit/mp_pf_icache_ctrl_unit.sv \
        ../deps/pulp_cluster/rtl/cluster_peripherals.sv \
        ../src/pkt_scheduler/cluster_rb.sv \
        ../src/pkt_scheduler/cluster_scheduler.sv \
        ../src/cmds/cluster_cmd.sv \
        ../deps/cluster_interconnect/rtl/interfaces/xbar_demux_bus.sv \
        ../deps/riscv/verilator-model/cluster_clock_gating.sv \
        ../deps/riscv/riscv_L0_buffer.sv \
        ../deps/riscv/riscv_prefetch_L0_buffer.sv \
        ../deps/riscv/riscv_hwloop_controller.sv \
        ../deps/riscv/riscv_compressed_decoder.sv \
        ../deps/riscv/riscv_if_stage.sv \
        ../deps/riscv/riscv_register_file.sv \
        ../deps/riscv/riscv_decoder.sv \
        ../deps/riscv/riscv_controller.sv \
        ../deps/riscv/riscv_int_controller.sv \
        ../deps/riscv/riscv_hwloop_regs.sv \
        ../deps/riscv/riscv_id_stage.sv \
        ../deps/riscv/riscv_popcnt.sv \
        ../deps/riscv/riscv_ff_one.sv \
        ../deps/riscv/riscv_alu_div.sv \
        ../deps/riscv/riscv_alu.sv \
        ../deps/riscv/riscv_mult.sv \
        ../deps/riscv/riscv_apu_disp.sv \
        ../deps/riscv/riscv_ex_stage.sv \
        ../deps/riscv/riscv_load_store_unit.sv \
        ../deps/riscv/riscv_cs_registers.sv \
        ../deps/riscv/riscv_pmp.sv \
        ../deps/riscv/include/riscv_tracer_defines.sv \
        ../deps/riscv/riscv_tracer.sv \
        ../deps/riscv/riscv_core.sv \
        ../deps/common_cells/src/deprecated/generic_fifo.sv \
        ../deps/pulp_cluster/rtl/periph_FIFO.sv \
        ../deps/pulp_cluster/rtl/core_demux.sv \
        ../deps/riscv/riscv_store_buffer.sv \
        ../deps/pulp_cluster/rtl/periph_demux.sv \
        ../deps/pulp_cluster/rtl/inter_core_fifo.sv \
        ../deps/pulp_cluster/rtl/virtual_stdout_demux.sv \
        ../deps/pulp_cluster/rtl/core_region.sv \
        ../src/pkt_scheduler/hpu_driver.sv \
        ../deps/common_cells/src/deprecated/generic_LFSR_8bit.sv \
        ../deps/common_cells/src/onehot_to_bin.sv \
        ../deps/icache_mp_128_pf/RTL/icache_bank_mp_128.sv \
        ../deps/scm/latch_scm/register_file_1w_multi_port_read.sv \
        ../deps/icache-intc/Req_Arb_Node_icache_intc.sv \
        ../deps/icache-intc/DistributedArbitrationNetwork_Req_icache_intc.sv \
        ../deps/icache-intc/RoutingBlock_Req_icache_intc.sv \
        ../deps/icache-intc/DistributedArbitrationNetwork_Resp_icache_intc.sv \
        ../deps/icache-intc/RoutingBlock_Resp_icache_intc.sv \
        ../deps/icache-intc/icache_intc.sv \
        ../deps/icache_mp_128_pf/RTL/pf_miss_mux.sv \
        ../deps/icache_mp_128_pf/RTL/merge_refill_cam_128_16.sv \
        ../deps/icache_mp_128_pf/RTL/central_controller_128.sv \
        ../deps/icache_mp_128_pf/RTL/cache_controller_to_axi_128_PF.sv \
        ../deps/icache_mp_128_pf/RTL/icache_bank_mp_PF.sv \
        ../deps/icache_mp_128_pf/RTL/prefetcher_if.sv \
        ../deps/icache_mp_128_pf/RTL/icache_top_mp_128_PF.sv \
        ../deps/axi/src/axi_cut.sv \
        ../deps/axi_slice_dc/src/dc_token_ring.v \
        ../deps/axi_slice_dc/src/dc_synchronizer.v \
        ../deps/axi_slice_dc/src/dc_token_ring_fifo_dout.v \
        ../deps/common_cells/src/edge_propagator_tx.sv \
        ../deps/pulp_cluster/rtl/pulp_cluster.sv \
        ../src/pulp_cluster_ooc.sv \
        ../src/memories/prog_mem.sv \
        ../deps/axi/src/axi_dw_upsizer.sv \
        ../deps/axi/src/axi_dw_converter.sv \
        ../src/interconnects/pe_noc.sv \
        ../src/interconnects/dma_noc.sv \
        ../src/interconnects/cluster_noc.sv \
        ../src/interconnects/l2_xbar.sv \
        ../deps/axi/src/axi_id_remap.sv \
        ../src/interconnects/nhi_xbar.sv \
        ../deps/axi_riscv_atomics/src/axi_riscv_amos_alu.sv \
        ../deps/axi_riscv_atomics/src/axi_riscv_amos.sv \
        ../deps/common_cells/src/id_queue.sv \
        ../deps/common_cells/src/stream_filter.sv \
        ../deps/common_cells/src/stream_arbiter_flushable.sv \
        ../deps/common_cells/src/stream_arbiter.sv \
        ../deps/axi_riscv_atomics/src/axi_res_tbl.sv \
        ../deps/axi_riscv_atomics/src/axi_riscv_lrsc.sv \
        ../deps/axi_riscv_atomics/src/axi_riscv_atomics.sv \
        ../deps/axi_riscv_atomics/src/axi_riscv_atomics_wrap.sv \
        ../deps/apb/src/apb_intf.sv \
        ../deps/axi2apb/src/axi2apb_64_32.sv \
        ../deps/axi2apb/src/axi2apb_wrap.sv \
        ../src/apb/apb_bus.sv \
        ../src/apb/apb_bus_wrap.sv \
        ../src/apb/apb_stdout.sv \
        ../src/apb/apb_ro_regs.sv \
        ../src/apb/apb_rw_regs.sv \
        ../src/soc_ctrl_regs.sv \
        ../src/soc_peripherals.sv \
		../deps/axi/src/axi_dw_downsizer.sv \
		../src/host_direct.sv \
 		../src/host_mst_mux.sv \
        ../src/pspin.sv \
        ../src/pspin_verilator.sv \

.PHONY: archive

debug:
	$(VERILATOR_CC) $(VFLAGS_DEBUG) $(SV_INC) -cc $(SV_SRCS) --top-module $(TOP_MODULE) --build $(SIM_LIB_SRCS) -o pspin
	@mkdir -p lib/
	$(CXX) $(LIB_DEBUG_FLAGS) -o lib/libpspin_debug.so $(SIM_LIB_SRCS) obj_dir_debug/Vpspin_verilator__ALL.a $(VERILATOR_ROOT)/include/verilated.cpp $(VERILATOR_ROOT)/include/verilated_vcd_c.cpp -Wl,--no-undefined

release:
	$(VERILATOR_CC) $(VFLAGS_RELEASE) $(SV_INC) -cc $(SV_SRCS) --top-module $(TOP_MODULE) --build $(SIM_LIB_SRCS) -o pspin
	@mkdir -p lib/
	$(CXX) $(LIB_RELEASE_FLAGS) -o lib/libpspin.so $(SIM_LIB_SRCS) obj_dir_release/Vpspin_verilator__ALL.a $(VERILATOR_ROOT)/include/verilated.cpp -Wl,--no-undefined

clean:
	@rm -rf obj_dir_debug/ obj_dir_release/ bin/pspin bin/pspin_debug lib/libpspin.so lib/libpspin_debug.so > /dev/null 2> /dev/null

pack:
	mkdir -p pspin-v${PSPIN_VERSION}/sim_files/slm_files/
	mkdir -p pspin-v${PSPIN_VERSION}/verilator_model/bin/
	mkdir -p pspin-v${PSPIN_VERSION}/verilator_model/lib/
	cp bin/pspin* pspin-v${PSPIN_VERSION}/verilator_model/bin/
	cp lib/lib* pspin-v${PSPIN_VERSION}/verilator_model/lib/
	cp -r include pspin-v${PSPIN_VERSION}/verilator_model/
	cp start_sim.sh pspin-v${PSPIN_VERSION}/verilator_model/
	tar -czvf pspin-v${PSPIN_VERSION}.tar.gz pspin-v${PSPIN_VERSION}/

.PHONY: lib/libpspin.so lib/libpspin_debug.so clean pack
