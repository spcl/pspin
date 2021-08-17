SPIN_APP_NAME = test
SPIN_APP_SRCS = handlers/test.c
SPIN_CFLAGS = -O3 -g ${DEFINITIONS}
SPIN_LDFLAGS = -lm -flto

include $(PSPIN_RT)/rules/spin-handlers.mk

DRIVER_CXX=g++
DRIVER_CXXFLAGS=-I ../include/ -I ../../../include/ -I ../obj_dir_release/ -I$(VERILATOR_HOME)/include -I$(VERILATOR_HOME)/include/vltstd
DRIVER_LDFLAGS=-L ../lib/ -lpspin_core
DRIVER_SRC=driver/coretest.cpp
DRIVER_NAME=test_driver

DRIVER_DBG_LDFLAGS=-L ../lib/ -lpspin_core_debug
DRIVER_DBG_NAME=test_driver_debug

driver: $(DRIVER_SRC)
	 $(DRIVER_CXX) $(DRIVER_CXXFLAGS) $(DRIVER_SRC) $(DRIVER_LDFLAGS) -o $(DRIVER_NAME)

driver_debug: $(DRIVER_SRC)
	 $(DRIVER_CXX) $(DRIVER_CXXFLAGS) $(DRIVER_SRC) $(DRIVER_DBG_LDFLAGS) -o $(DRIVER_DBG_NAME)
