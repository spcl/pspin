#ModelSim
#export PSPIN_SIM="modelsim_model"

#Verilator
export PSPIN_SIM="verilator_model"

#Update these!
export RISCV_GCC=
export PSPIN_HW=
export PSPIN_RT=

#Don't change
export TARGET_VSIM=${PSPIN_HW}/$PSPIN_SIM
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/${PSPIN_HW}/verilator_model/lib/
export TRACE_DIR="./"

