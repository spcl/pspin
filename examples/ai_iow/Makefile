SPIN_APP_NAME = synthetic
SPIN_APP_SRCS = handlers/synthetic.c
SPIN_CFLAGS = -O3 -g ${DEFINITIONS}
SPIN_LDFLAGS = -lm -flto

include $(PSPIN_RT)/rules/spin-handlers.mk
include ../generic_driver/gdriver.mk
