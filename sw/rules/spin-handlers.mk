TARGET_SLM ?= ${PSPIN_HW}/sim_files/slm_files
TARGET_VSIM ?= ${PSPIN_HW}/${PSPIN_SIM}
SPIN_APP_NAME ?= ""
TELEMETRY_KEY ?= ""
INFO_KEY ?= ""
DMA_KEY ?= ""
HANDLERS_PREFIX ?= ${SPIN_APP_NAME}
PKT_SIZE ?= 1024
PKT_DELAY ?= 78
MSG_DELAY ?= 78

include $(PSPIN_RT)/rules/spin-rt.mk

#0: only header; 1: transfer full packet; 2: custom transfer
FULL_PKT ?= 0
CUSTOM_HDR_SIZE ?= 0

PKT_SEED ?= 0
HAS_HH ?= 1
HAS_TH ?= 1
MSG_COUNT ?= 1
PKTGEN_CUSTOM_PARAMS ?= ""
APP_CFLAGS ?= ""

PKTGEN ?= ${PSPIN_RT}/packet_generator/bin/generic

# Default rule
all::

build::
	$(MAKE) conf io=uart CONFIG_OPT="uart/baudrate=115200"

packets::
	$(PSPIN_RT)/scripts/make_packets.sh ${NUM_PACKETS} ${SPIN_APP_NAME} ${HANDLERS_PREFIX} ${PKT_SIZE} ${PKT_DELAY} ${MSG_DELAY} ${FULL_PKT} ${MSG_COUNT} ${PKTGEN} ${PKTGEN_CUSTOM_PARAMS} ${HAS_HH} ${HAS_TH} ${PKT_SEED} ${CUSTOM_HDR_SIZE}

#TODO: trace, trace-chrome should go to stdout, not to a file! 
trace::
	perl $(PSPIN_RT)/scripts/tracevis/parse.pl -t build/$(SPIN_APP_NAME) $(TRACE_DIR)trace_core_* > $(SPIN_APP_NAME).trace.txt

transcript::
	cat $(TARGET_VSIM)/transcript

trace-chrome::
	perl $(PSPIN_RT)/scripts/tracevis/parse.pl  build/$(SPIN_APP_NAME) $(TRACE_DIR)trace_core_* > $(SPIN_APP_NAME).trace.json

trace-stdout::
	@perl $(PSPIN_RT)/scripts/tracevis/parse.pl -t build/$(SPIN_APP_NAME) $(TARGET_VSIM)/trace_core_*

trace-chrome-stdout::
	@perl $(PSPIN_RT)/scripts/tracevis/parse.pl build/$(SPIN_APP_NAME) $(TARGET_VSIM)/trace_core_*

#telemetry::
#	$(PSPIN_RT)/scripts/telemetry_time_tracevis.sh $(SPIN_APP_NAME).trace.txt $(TELEMETRY_KEY) "$(PSPIN_RT)/src/*.c ${SPIN_APP_SRCS}" > $(SPIN_APP_NAME).time.telemetry

#telemetry-instr::
#	$(PSPIN_RT)/scripts/telemetry_instructions_tracevis.sh $(SPIN_APP_NAME).trace.txt $(TELEMETRY_KEY) "$(PSPIN_RT)/src/*.c ${SPIN_APP_SRCS}" > $(SPIN_APP_NAME).instructions.telemetry

#info::
#	$(PSPIN_RT)/scripts/extract_info.sh $(INFO_KEY) $(TARGET_VSIM)/transcript
#

info::
	make trace;
	$(PSPIN_RT)/scripts/handlers_data.sh $(INFO_KEY) $(SPIN_APP_NAME).trace.txt

dma::
	$(PSPIN_RT)/scripts/extract_dma.sh $(DMA_KEY) $(TARGET_VSIM)

patch:
	@for file in ${PATCH_INTERNAL} ${PATCH_EXTERNAL}; do \
		$(PSPIN_RT)/scripts/patch_bsw.sh $${file} build/bigpulp-juno/${SPIN_APP_NAME}/cl/${PSPIN_RT}/src/ "${PULP_CFLAGS}" ; \
	done

simulate::
	$(PSPIN_RT)/scripts/spin_run.sh 0 | tee transcript
	cp $(PSPIN_HW)/verilator_model/trace_* .

simulate-debug::
	$(PSPIN_RT)/scripts/spin_run.sh 1 | tee transcript
	cp $(PSPIN_HW)/verilator_model/trace_* .
	cp $(PSPIN_HW)/verilator_model/waves.vcd .

stats::
	$(PSPIN_RT)/scripts/handlers_duration.sh transcript

makenrun::
	make patch
	make deploy
	make packets
	make simulate


