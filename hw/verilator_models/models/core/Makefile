PSPIN_VERSION ?= undef
VERILATOR_CMD ?= verilator
VERILATOR_CC=$(VERILATOR_BIN)$(VERILATOR_CMD)
TOP_MODULE=pspin_verilator
SIM_LIB_SRCS=src/pspincoresim.cpp

CXX ?= g++
VERILATOR_COMPILER_WORKERS ?= 8

TRACE_DEPTH?=6
VFLAGS_RELEASE=--Mdir obj_dir_release --sv -Wno-UNOPTFLAT -Wno-NOLATCH -Wno-WIDTHCONCAT -j $(VERILATOR_COMPILER_WORKERS) +systemverilogext+sv -Wno-lint -CFLAGS "-fPIC"
VFLAGS_DEBUG=--Mdir obj_dir_debug --sv --assert --trace --trace-structs --trace-depth $(TRACE_DEPTH) -CFLAGS "-DVERILATOR_HAS_TRACE -fPIC" -Wno-UNOPTFLAT -Wno-NOLATCH -Wno-WIDTHCONCAT -j $(VERILATOR_COMPILER_WORKERS) +systemverilogext+sv -Wno-lint


LIB_RELEASE_FLAGS=-fPIC -g --std=c++11 -Os -shared -Iobj_dir_release -I$(HW_ROOT)/verilator_models/include/ -I$(VERILATOR_ROOT)/include -I$(VERILATOR_ROOT)/include/vltstd/ -Iinclude/ 
LIB_DEBUG_FLAGS=-fPIC -g --std=c++11 -Os -shared -Iobj_dir_debug -I$(HW_ROOT)/verilator_models/include/ -I$(VERILATOR_ROOT)/include -I$(VERILATOR_ROOT)/include/vltstd/ -Iinclude/ -DVERILATOR_HAS_TRACE

EXE_RELEASE_FLAGS=-Iinclude/
EXE_DEBUG_FLAGS=-Iinclude/ -DVERILATOR_HAS_TRACE

HW_ROOT=../../../

SV_INC=-I$(HW_ROOT)/deps/axi/include/ -I$(HW_ROOT)/deps/common_cells/include -I$(HW_ROOT)/deps/cluster_interconnect/rtl/low_latency_interco/ -I$(HW_ROOT)/deps/riscv/include/
SV_SRCS=$(HW_ROOT)/deps/axi/src/axi_pkg.sv \
        $(HW_ROOT)/deps/axi/src/axi_intf.sv \
        $(HW_ROOT)/src/pulp_cluster_cfg_pkg.sv \
        $(HW_ROOT)/src/pspin_cfg_pkg.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/tcdm_interconnect/tcdm_interconnect_pkg.sv \
        $(HW_ROOT)/deps/common_cells/src/fifo_v3.sv \
        $(HW_ROOT)/deps/common_cells/src/stream_fifo.sv \
        $(HW_ROOT)/deps/axi/src/axi_buf.sv \
        $(HW_ROOT)/deps/common_cells/src/delta_counter.sv \
        $(HW_ROOT)/deps/common_cells/src/cf_math_pkg.sv \
        $(HW_ROOT)/deps/common_cells/src/lzc.sv \
        $(HW_ROOT)/deps/common_cells/src/rr_arb_tree.sv \
        $(HW_ROOT)/deps/common_cells/src/spill_register.sv \
        $(HW_ROOT)/deps/axi/src/axi_demux.sv \
        $(HW_ROOT)/deps/riscv/include/fpnew_pkg.sv \
        $(HW_ROOT)/deps/riscv/include/riscv_defines.sv \
        $(HW_ROOT)/deps/common_cells/src/deprecated/fifo_v2.sv \
        $(HW_ROOT)/deps/common_cells/src/fall_through_register.sv \
        $(HW_ROOT)/deps/common_cells/src/stream_demux.sv \
        $(HW_ROOT)/deps/common_cells/src/stream_mux.sv \
        $(HW_ROOT)/deps/common_cells/src/stream_fork.sv \
        $(HW_ROOT)/deps/common_cells/src/stream_fork_dynamic.sv \
        $(HW_ROOT)/deps/common_cells/src/stream_to_mem.sv \
        $(HW_ROOT)/deps/common_cells/src/stream_join.sv \
        $(HW_ROOT)/deps/axi2mem/src/axi_to_mem.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/tcdm_interconnect/addr_dec_resp_mux.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/tcdm_interconnect/xbar.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/tcdm_interconnect/tcdm_interconnect.sv \
        $(HW_ROOT)/deps/axi2mem/src/axi_to_mem_banked_mp.sv \
        $(HW_ROOT)/deps/tech_cells_generic/src/rtl/tc_sram.sv \
        $(HW_ROOT)/src/memories/sram.sv \
        $(HW_ROOT)/src/memories/l2_mem.sv \
        $(HW_ROOT)/src/pkt_scheduler/fifo_engine.sv \
        $(HW_ROOT)/src/pkt_scheduler/mpq_engine.sv \
        $(HW_ROOT)/src/pkt_scheduler/scheduler.sv \
        $(HW_ROOT)/deps/axi/src/dma/axi_dma_burst_reshaper.sv \
        $(HW_ROOT)/deps/axi/src/dma/axi_dma_data_path \
        $(HW_ROOT)/deps/axi/src/dma/axi_dma_data_mover.sv \
        $(HW_ROOT)/deps/axi/src/dma/axi_dma_backend.sv \
        $(HW_ROOT)/deps/common_cells/src/addr_decode.sv \
        $(HW_ROOT)/deps/common_cells/src/stream_register.sv \
        $(HW_ROOT)/deps/common_cells/src/counter.sv \
        $(HW_ROOT)/deps/axi/src/axi_atop_filter.sv \
        $(HW_ROOT)/deps/axi/src/axi_err_slv.sv \
        $(HW_ROOT)/deps/axi/src/axi_id_prepend.sv \
        $(HW_ROOT)/deps/axi/src/axi_mux.sv \
        $(HW_ROOT)/deps/axi/src/axi_xbar.sv \
        $(HW_ROOT)/deps/axi/src/dma/frontends/pspin_soc_frontend/src/pspin_soc_dma.sv \
        $(HW_ROOT)/src/soc_dma_wrap.sv \
        $(HW_ROOT)/src/cmds/cmd_unit.sv \
        $(HW_ROOT)/deps/pulp_cluster/packages/pulp_cluster_package.sv \
        $(HW_ROOT)/deps/riscv/include/apu_core_package.sv \
        $(HW_ROOT)/deps/pulp_cluster/packages/apu_package.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/interfaces/xbar_tcdm_bus.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/interfaces/xbar_periph_bus.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/cpu_marx_if.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/interfaces/tcdm_bank_mem_bus.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/interfaces/wide_dma_tcdm.sv \
        $(HW_ROOT)/deps/cluster_peripherals/icache_ctrl_unit/interfaces/mp_pf_icache_ctrl_unit_bus.sv \
        $(HW_ROOT)/deps/common_cells/src/rstgen_bypass.sv \
        $(HW_ROOT)/deps/common_cells/src/rstgen.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/cluster_bus_wrap.sv \
        $(HW_ROOT)/deps/axi_slice/src/axi_w_buffer.sv \
        $(HW_ROOT)/deps/axi_slice/src/axi_r_buffer.sv \
        $(HW_ROOT)/deps/axi_slice/src/axi_ar_buffer.sv \
        $(HW_ROOT)/deps/axi_slice/src/axi_b_buffer.sv \
        $(HW_ROOT)/deps/common_cells/src/deprecated/fifo_v1.sv \
        $(HW_ROOT)/deps/axi_slice/src/axi_single_slice.sv \
        $(HW_ROOT)/deps/axi_slice/src/axi_aw_buffer.sv \
        $(HW_ROOT)/deps/axi2per/axi2per_req_channel.sv \
        $(HW_ROOT)/deps/axi2per/axi2per_res_channel.sv \
        $(HW_ROOT)/deps/axi2per/axi2per.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/axi2per_wrap.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/per_demux_wrap.sv \
        $(HW_ROOT)/deps/per2axi/src/per2axi_req_channel.sv \
        $(HW_ROOT)/deps/per2axi/src/per2axi_res_channel.sv \
        $(HW_ROOT)/deps/per2axi/src/per2axi_busy_unit.sv \
        $(HW_ROOT)/deps/per2axi/src/per2axi.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/per2axi_wrap.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/tryx_ctrl.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/tcdm_interconnect/superbank_addr_decoder.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/tcdm_interconnect/tcdm_superbank_mux.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/tcdm_interconnect/amo_shim.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/peripheral_interco/FanInPrimitive_Req_PE.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/peripheral_interco/RR_Flag_Req_PE \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/peripheral_interco/ArbitrationTree_PE.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/peripheral_interco/MUX2_REQ_PE.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/peripheral_interco/AddressDecoder_Resp_PE.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/peripheral_interco/RequestBlock2CH_PE.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/peripheral_interco/FanInPrimitive_PE_Resp \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/peripheral_interco/ResponseTree_PE.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/peripheral_interco/AddressDecoder_PE_Req.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/peripheral_interco/ResponseBlock_PE.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/peripheral_interco/XBAR_PE.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/cluster_interconnect_wrap.sv \
        $(HW_ROOT)/deps/axi/src/axi_serializer.sv \
        $(HW_ROOT)/deps/axi/src/dma/frontends/pulp_cluster_frontend/src/transfer_id_gen.sv \
        $(HW_ROOT)/deps/axi/src/dma/frontends/pulp_cluster_frontend/src/pulp_cluster_frontend_regs.sv \
        $(HW_ROOT)/deps/axi/src/dma/frontends/pulp_cluster_frontend/src/pulp_cluster_frontend.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/dmac_wrap.sv \
		$(HW_ROOT)/deps/axi2mem/src/axi_to_mem_interleaved.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/nhi_port_wrap.sv \
        $(HW_ROOT)/deps/event_unit_flex/message_bus.sv \
        $(HW_ROOT)/deps/cluster_peripherals/cluster_control_unit/cluster_control_unit.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/cluster_timer_wrap.sv \
        $(HW_ROOT)/deps/timer_unit/rtl/timer_unit_counter_presc.sv \
        $(HW_ROOT)/deps/timer_unit/rtl/timer_unit_counter.sv \
        $(HW_ROOT)/deps/timer_unit/rtl/timer_unit.sv \
        $(HW_ROOT)/deps/event_unit_flex/event_unit_interface_mux.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/cluster_event_map.sv \
        $(HW_ROOT)/deps/event_unit_flex/interc_sw_evt_trig.sv \
        $(HW_ROOT)/deps/event_unit_flex/event_unit_core.sv \
        $(HW_ROOT)/deps/event_unit_flex/hw_barrier_unit.sv \
        $(HW_ROOT)/deps/event_unit_flex/hw_mutex_unit.sv \
        $(HW_ROOT)/deps/event_unit_flex/hw_dispatch.sv \
        $(HW_ROOT)/deps/event_unit_flex/event_unit_top.sv \
        $(HW_ROOT)/deps/cluster_peripherals/icache_ctrl_unit/mp_pf_icache_ctrl_unit.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/cluster_peripherals.sv \
        $(HW_ROOT)/src/pkt_scheduler/cluster_rb.sv \
        $(HW_ROOT)/src/pkt_scheduler/cluster_scheduler.sv \
        $(HW_ROOT)/src/cmds/cluster_cmd.sv \
        $(HW_ROOT)/deps/cluster_interconnect/rtl/interfaces/xbar_demux_bus.sv \
        $(HW_ROOT)/deps/riscv/verilator-model/cluster_clock_gating.sv \
        $(HW_ROOT)/deps/riscv/riscv_L0_buffer.sv \
        $(HW_ROOT)/deps/riscv/riscv_prefetch_L0_buffer.sv \
        $(HW_ROOT)/deps/riscv/riscv_hwloop_controller.sv \
        $(HW_ROOT)/deps/riscv/riscv_compressed_decoder.sv \
        $(HW_ROOT)/deps/riscv/riscv_if_stage.sv \
        $(HW_ROOT)/deps/riscv/riscv_register_file.sv \
        $(HW_ROOT)/deps/riscv/riscv_decoder.sv \
        $(HW_ROOT)/deps/riscv/riscv_controller.sv \
        $(HW_ROOT)/deps/riscv/riscv_int_controller.sv \
        $(HW_ROOT)/deps/riscv/riscv_hwloop_regs.sv \
        $(HW_ROOT)/deps/riscv/riscv_id_stage.sv \
        $(HW_ROOT)/deps/riscv/riscv_popcnt.sv \
        $(HW_ROOT)/deps/riscv/riscv_ff_one.sv \
        $(HW_ROOT)/deps/riscv/riscv_alu_div.sv \
        $(HW_ROOT)/deps/riscv/riscv_alu.sv \
        $(HW_ROOT)/deps/riscv/riscv_mult.sv \
        $(HW_ROOT)/deps/riscv/riscv_apu_disp.sv \
        $(HW_ROOT)/deps/riscv/riscv_ex_stage.sv \
        $(HW_ROOT)/deps/riscv/riscv_load_store_unit.sv \
        $(HW_ROOT)/deps/riscv/riscv_cs_registers.sv \
        $(HW_ROOT)/deps/riscv/riscv_pmp.sv \
        $(HW_ROOT)/deps/riscv/include/riscv_tracer_defines.sv \
        $(HW_ROOT)/deps/riscv/riscv_tracer.sv \
        $(HW_ROOT)/deps/riscv/riscv_core.sv \
        $(HW_ROOT)/deps/common_cells/src/deprecated/generic_fifo.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/periph_FIFO.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/core_demux.sv \
        $(HW_ROOT)/deps/riscv/riscv_store_buffer.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/periph_demux.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/inter_core_fifo.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/virtual_stdout_demux.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/core_region.sv \
        $(HW_ROOT)/src/pkt_scheduler/hpu_driver.sv \
        $(HW_ROOT)/deps/common_cells/src/deprecated/generic_LFSR_8bit.sv \
        $(HW_ROOT)/deps/common_cells/src/onehot_to_bin.sv \
        $(HW_ROOT)/deps/icache_mp_128_pf/RTL/icache_bank_mp_128.sv \
        $(HW_ROOT)/deps/scm/latch_scm/register_file_1w_multi_port_read.sv \
        $(HW_ROOT)/deps/icache-intc/Req_Arb_Node_icache_intc.sv \
        $(HW_ROOT)/deps/icache-intc/DistributedArbitrationNetwork_Req_icache_intc.sv \
        $(HW_ROOT)/deps/icache-intc/RoutingBlock_Req_icache_intc.sv \
        $(HW_ROOT)/deps/icache-intc/DistributedArbitrationNetwork_Resp_icache_intc.sv \
        $(HW_ROOT)/deps/icache-intc/RoutingBlock_Resp_icache_intc.sv \
        $(HW_ROOT)/deps/icache-intc/icache_intc.sv \
        $(HW_ROOT)/deps/icache_mp_128_pf/RTL/pf_miss_mux.sv \
        $(HW_ROOT)/deps/icache_mp_128_pf/RTL/merge_refill_cam_128_16.sv \
        $(HW_ROOT)/deps/icache_mp_128_pf/RTL/central_controller_128.sv \
        $(HW_ROOT)/deps/icache_mp_128_pf/RTL/cache_controller_to_axi_128_PF.sv \
        $(HW_ROOT)/deps/icache_mp_128_pf/RTL/icache_bank_mp_PF.sv \
        $(HW_ROOT)/deps/icache_mp_128_pf/RTL/prefetcher_if.sv \
        $(HW_ROOT)/deps/icache_mp_128_pf/RTL/icache_top_mp_128_PF.sv \
        $(HW_ROOT)/deps/axi/src/axi_cut.sv \
        $(HW_ROOT)/deps/axi_slice_dc/src/dc_token_ring.v \
        $(HW_ROOT)/deps/axi_slice_dc/src/dc_synchronizer.v \
        $(HW_ROOT)/deps/axi_slice_dc/src/dc_token_ring_fifo_dout.v \
        $(HW_ROOT)/deps/common_cells/src/edge_propagator_tx.sv \
        $(HW_ROOT)/deps/pulp_cluster/rtl/pulp_cluster.sv \
        $(HW_ROOT)/src/pulp_cluster_ooc.sv \
        $(HW_ROOT)/src/memories/prog_mem.sv \
        $(HW_ROOT)/deps/axi/src/axi_dw_upsizer.sv \
        $(HW_ROOT)/deps/axi/src/axi_dw_converter.sv \
        $(HW_ROOT)/src/interconnects/pe_noc.sv \
        $(HW_ROOT)/src/interconnects/dma_noc.sv \
        $(HW_ROOT)/src/interconnects/cluster_noc.sv \
        $(HW_ROOT)/src/interconnects/l2_xbar.sv \
        $(HW_ROOT)/deps/axi/src/axi_id_remap.sv \
        $(HW_ROOT)/src/interconnects/nhi_xbar.sv \
        $(HW_ROOT)/deps/axi_riscv_atomics/src/axi_riscv_amos_alu.sv \
        $(HW_ROOT)/deps/axi_riscv_atomics/src/axi_riscv_amos.sv \
        $(HW_ROOT)/deps/common_cells/src/id_queue.sv \
        $(HW_ROOT)/deps/common_cells/src/stream_filter.sv \
        $(HW_ROOT)/deps/common_cells/src/stream_arbiter_flushable.sv \
        $(HW_ROOT)/deps/common_cells/src/stream_arbiter.sv \
        $(HW_ROOT)/deps/axi_riscv_atomics/src/axi_res_tbl.sv \
        $(HW_ROOT)/deps/axi_riscv_atomics/src/axi_riscv_lrsc.sv \
        $(HW_ROOT)/deps/axi_riscv_atomics/src/axi_riscv_atomics.sv \
        $(HW_ROOT)/deps/axi_riscv_atomics/src/axi_riscv_atomics_wrap.sv \
        $(HW_ROOT)/deps/apb/src/apb_intf.sv \
        $(HW_ROOT)/deps/axi2apb/src/axi2apb_64_32.sv \
        $(HW_ROOT)/deps/axi2apb/src/axi2apb_wrap.sv \
        $(HW_ROOT)/src/apb/apb_bus.sv \
        $(HW_ROOT)/src/apb/apb_bus_wrap.sv \
        $(HW_ROOT)/src/apb/apb_stdout.sv \
        $(HW_ROOT)/src/apb/apb_ro_regs.sv \
        $(HW_ROOT)/src/apb/apb_rw_regs.sv \
        $(HW_ROOT)/src/soc_ctrl_regs.sv \
        $(HW_ROOT)/src/soc_peripherals.sv \
		$(HW_ROOT)/deps/axi/src/axi_dw_downsizer.sv \
		$(HW_ROOT)/src/host_direct.sv \
 		$(HW_ROOT)/src/host_mst_mux.sv \
        $(HW_ROOT)/src/pspin.sv \
        $(HW_ROOT)/src/pspin_verilator.sv \

.PHONY: archive

debug:
	$(VERILATOR_CC) $(VFLAGS_DEBUG) $(SV_INC) -cc $(SV_SRCS) --top-module $(TOP_MODULE) --build $(SIM_LIB_SRCS) -o pspin
	@mkdir -p lib/
	$(CXX) $(LIB_DEBUG_FLAGS) -o lib/libpspin_core_debug.so $(SIM_LIB_SRCS) obj_dir_debug/Vpspin_verilator__ALL.a $(VERILATOR_ROOT)/include/verilated.cpp $(VERILATOR_ROOT)/include/verilated_vcd_c.cpp

release:
	$(VERILATOR_CC) $(VFLAGS_RELEASE) $(SV_INC) -cc $(SV_SRCS) --top-module $(TOP_MODULE) --build $(SIM_LIB_SRCS) -o pspin
	@mkdir -p lib/
	$(CXX) $(LIB_RELEASE_FLAGS) -o lib/libpspin_core.so $(SIM_LIB_SRCS) obj_dir_release/Vpspin_verilator__ALL.a $(VERILATOR_ROOT)/include/verilated.cpp 

clean:
	@rm -rf obj_dir_debug/ obj_dir_release/ bin/pspin bin/pspin_debug lib/libpspin_core.so lib/libpspin_core_debug.so > /dev/null 2> /dev/null

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
