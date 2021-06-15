PSPIN_VERSION ?= undef
VERILATOR_CMD ?= verilator
VERILATOR_CC=$(VERILATOR_BIN)$(VERILATOR_CMD)
TOP_MODULE=pspin_verilator
SIM_LIB_SRCS=src/pspinsim.cpp

CXX ?= g++
VERILATOR_COMPILER_WORKERS ?= 8
BENDER ?= ../../utils/bender

TRACE_DEPTH?=6

VLT_FLAGS    += -Wno-BLKANDNBLK
VLT_FLAGS    += -Wno-LITENDIAN
VLT_FLAGS    += -Wno-CASEINCOMPLETE
VLT_FLAGS    += -Wno-CMPCONST
VLT_FLAGS    += -Wno-WIDTH
VLT_FLAGS    += -Wno-WIDTHCONCAT
VLT_FLAGS    += -Wno-UNSIGNED
VLT_FLAGS    += -Wno-UNOPTFLAT
VLT_FLAGS    += -Wno-NOLATCH
VLT_FLAGS    += -Wno-fatal

VFLAGS_RELEASE=--Mdir obj_dir_release --sv $(VLT_FLAGS) -j $(VERILATOR_COMPILER_WORKERS) +systemverilogext+sv -Wno-lint -CFLAGS "-fPIC"
VFLAGS_DEBUG=--Mdir obj_dir_debug --sv --assert --trace --trace-structs --trace-depth $(TRACE_DEPTH) -CFLAGS "-DVERILATOR_HAS_TRACE -fPIC" $(VLT_FLAGS) -j $(VERILATOR_COMPILER_WORKERS) +systemverilogext+sv -Wno-lint


LIB_RELEASE_FLAGS=-fPIC --std=c++11 -Os -shared -Iobj_dir_release -I$(VERILATOR_ROOT)/include -I$(VERILATOR_ROOT)/include/vltstd/ -Iinclude/ 
LIB_DEBUG_FLAGS=-fPIC -g --std=c++11 -Os -shared -Iobj_dir_debug -I$(VERILATOR_ROOT)/include -I$(VERILATOR_ROOT)/include/vltstd/ -Iinclude/ -DVERILATOR_HAS_TRACE

EXE_RELEASE_FLAGS=-Iinclude/
EXE_DEBUG_FLAGS=-Iinclude/ -DVERILATOR_HAS_TRACE

SV_INC=-I../deps/axi/include/ -I../deps/common_cells/include -I../deps/cluster_interconnect/rtl/low_latency_interco/ -I../deps/riscv/include/
SV_SRCS=$(shell cd ..; ${BENDER} script verilator -t rtl -t verilator)

.PHONY: archive

debug:
	$(VERILATOR_CC) $(VFLAGS_DEBUG) $(SV_INC) -cc $(SV_SRCS) --top-module $(TOP_MODULE) --build $(SIM_LIB_SRCS) -o pspin
	@mkdir -p lib/
	$(CXX) $(LIB_DEBUG_FLAGS) -o lib/libpspin_debug.so $(SIM_LIB_SRCS) obj_dir_debug/Vpspin_verilator__ALL.a $(VERILATOR_ROOT)/include/verilated.cpp $(VERILATOR_ROOT)/include/verilated_vcd_c.cpp

release:
	$(VERILATOR_CC) $(VFLAGS_RELEASE) $(SV_INC) -cc $(SV_SRCS) --top-module $(TOP_MODULE) --build $(SIM_LIB_SRCS) -o pspin
	@mkdir -p lib/
	$(CXX) $(LIB_RELEASE_FLAGS) -o lib/libpspin.so $(SIM_LIB_SRCS) obj_dir_release/Vpspin_verilator__ALL.a $(VERILATOR_ROOT)/include/verilated.cpp 

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
