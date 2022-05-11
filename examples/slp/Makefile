SPIN_APP_NAME = slp_l1
SPIN_APP_SRCS = handlers/slp_l1.c
SPIN_CFLAGS = -O3 -g -flto -DVECTOR_LEN=$(VLEN) -DDTYPE=$(DTYPE)
SPIN_LDFLAGS = -lm

include $(PSPIN_RT)/rules/spin-handlers.mk
include ../generic_driver/gdriver.mk
