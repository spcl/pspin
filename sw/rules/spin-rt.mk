TARGET_SLM ?= ${PSPIN_HW}/sim_files/slm_files
CC=${RISCV_GCC}/riscv32-unknown-elf-gcc
OBJCOPY=${RISCV_GCC}/riscv32-unknown-elf-objcopy
OBJDUMP=${RISCV_GCC}/riscv32-unknown-elf-objdump
PULP_SDK=${PSPIN_RT}/pulp-sdk/

TARGET_BIN=build/$(SPIN_APP_NAME)

.PHONY: install deploy

CFLAGS=-DPULP_CHIP_STR=bigpulp -DPULP_CHIP_FAMILY_STR=bigpulp -DPULP_CHIP=40 -DPULP_CHIP_FAMILY=7 -march=rv32imacxpulpv2 -D__riscv__ -MMD -MP $(SPIN_CFLAGS)
LDFLAGS=-nostartfiles -nostdlib -Wl,--gc-sections -T $(PULP_SDK)/linker/config.ld -T $(PULP_SDK)/linker/link.ld $(SPIN_LDFLAGS)
INCLUDE_FILES=-I$(PULP_SDK)/archi/include -I$(PULP_SDK)/hal/include -I${PSPIN_HW}/deps/axi/src/dma/frontends/pulp_cluster_frontend/lib/ -I${PSPIN_RT}/include/

PULP_SRCS=$(PULP_SDK)/runtime/libs/io/io.c $(PULP_SDK)/runtime/libs/io/tinyprintf.c
PULP_INC=-I$(PULP_SDK)/runtime/libs/io/

#SRC_FILES=$(PSPIN_RT)/src/hpu.c $(PSPIN_RT)/src/handler.c ${SPIN_APP_SRCS}
SRC_FILES=$(PSPIN_RT)/src/hpu.c ${SPIN_APP_SRCS}


runtime-debug: 
	mkdir -p build/
	$(CC) $(CFLAGS) -DLANGUAGE_ASSEMBLY $(INCLUDE_FILES) -c $(PULP_SDK)/kernel/riscv/rt/crt0.S -o build/crt0.o
	$(CC) $(CFLAGS) ${SPIN_CFLAGS} $(PULP_INC) $(INCLUDE_FILES) $(PULP_SRCS) $(SRC_FILES) build/crt0.o -o $(TARGET_BIN) $(LDFLAGS)

runtime: 
	mkdir -p build/
	$(CC) $(CFLAGS) -DLANGUAGE_ASSEMBLY -O3 -flto $(INCLUDE_FILES) -c $(PULP_SDK)/kernel/riscv/rt/crt0.S -o build/crt0.o
	$(CC) $(CFLAGS) ${SPIN_CFLAGS} $(PULP_INC) $(INCLUDE_FILES) $(PULP_SRCS) $(SRC_FILES) build/crt0.o -o $(TARGET_BIN) $(LDFLAGS)

deploy::
	$(MAKE) runtime
	mkdir -p build/slm_files/
	$(OBJCOPY) --srec-len 1 --output-target=srec $(TARGET_BIN) build/$(SPIN_APP_NAME).s19
	cd build/slm_files && \
	$(PULP_SDK)/scripts/s19toslm.py ../$(SPIN_APP_NAME).s19 && \
	$(PULP_SDK)/bin/slm_conv -n 16384 -f l2_hnd_stim.slm -S 1 -P 32 && \
	python $(PULP_SDK)/bin/rename_l2.py hnd && \
	mkdir -p ${TARGET_SLM} && \
	cp *.slm ${TARGET_SLM} 
	$(OBJDUMP) -S build/$(SPIN_APP_NAME) > build/$(SPIN_APP_NAME).disasm

install:
	mkdir -p build/
	mkdir -p build/lib/
	mkdir -p build/include/
	(cd packet_generator; make lib )
	cp packet_generator/libpktgen.so build/lib/
	cp packet_generator/*.h build/include/


