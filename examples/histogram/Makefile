SPIN_APP_NAME = histogram_l1
SPIN_APP_SRCS = histogram_l1.c
SPIN_CFLAGS = -O3 -g -flto
SPIN_LDFLAGS = -lm 
NUM_PACKETS ?=512
HAS_HH ?= 0
HAS_TH ?= 1
FULL_PKT = 1
MSG_COUNT ?=1
PKT_DELAY ?= 0
MSG_DELAY ?= 0
PKT_SIZE ?= 1024
PKTGEN_CUSTOM_PARAMS="--fill-mod 1024"
include $(PSPIN_RT)/spin-handlers.mk

