SPIN_APP_NAME = reduce
SPIN_APP_SRCS = handlers/reduce.c
SPIN_CFLAGS = -O3 -g ${DEFINITIONS}
SPIN_LDFLAGS = -lm -flto

include $(PSPIN_RT)/rules/spin-handlers.mk
include ../generic_driver/gdriver.mk
