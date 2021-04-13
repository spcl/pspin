SPIN_APP_NAME = htable
SPIN_APP_SRCS = htable_handlers.c
SPIN_CFLAGS = -O3 -g ${DEFINITIONS}
SPIN_LDFLAGS = -lm -flto
NUM_PACKETS ?= 4
PKT_DELAY ?= 0
MSG_DELAY ?= 0


include $(PSPIN_RT)/spin-handlers.mk

all::
	make deploy
	make driver

driver: htable_driver.c
	 gcc -std=c99 -I$(PSPIN_RT)/include/ -I$(PSPIN_HW)/verilator_model/include htable_driver.c -L$(PSPIN_HW)/verilator_model/lib/ -lpspin_debug -o htable_driver
