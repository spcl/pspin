# Manual installation

Verilating the hardware is needed whenever you want test new hardware changes that are not available in the relased packeges. The verilation process can take quite long time (20-30 minutes on a Xeon X7550) and can require up to 16 GB of memory. Consider using the docker image if that fits your use case.

### Requirements
Verilator >= 4.108

### Clone the repository

```bash
git clone https://github.com/spcl/pspin
```

### Setting up the environment 
 Copy the `sourceme-template.sh` file to `sourceme.sh`:
 
```bash
 cp sourceme-template.sh sourceme.sh
```
 
Update the following variables:

```bash
export RISCV_GCC=<path to the RISC-V GCC toolchain binaries, e.g., /home/salvo/riscv-gcc/bin/>
export PSPIN_HW=<path to the hw, e.g., /home/salvo/pspin/hw/>
export PSPIN_RT=<path to the sw, e.g., /home/salvo/pspin/sw/>
```

**Source this file every time you want to run simulations!**
```bash 
source sourceme.sh
```

### Verilate the hardware

Define `VERILATOR_HOME`:
```bash
export VERILATOR_HOME=<path to verilator installation>
```

Compile `libpspin`:
```bash
cd hw/verilator_model/

# Compile `libpspin.so`
make release

# (Optional) Compile `libpspin_debug.so`
make debug
```


