SPIN_APP_NAME = hostdirect
SPIN_APP_SRCS = hostdirect.c
SPIN_CFLAGS = -O3 -g ${DEFINITIONS}
SPIN_LDFLAGS = -lm -flto
NUM_PACKETS ?= 512
PKT_DELAY ?= 0
MSG_DELAY ?= 0


include $(PSPIN_RT)/spin-handlers.mk

