# Verilating the hardware

Verilating the hardware is needed whenever you want test new hardware changes that are not available in the relased packeges. The verilation process can take quite long time (20-30 minutes on a Xeon X7550) and can require up to 16 GB of memory. Consider to use the prebuilt libraries if they fit your use case. 

### Requirements:
Verilator >= 4.108

### 1) Clone the repository

```bash
git clone https://github.com/spcl/pspin
```

### 2) Define `VERILATOR_HOME`
```bash
export VERILATOR_HOME=<path to verilator installation>
```

### 3) Verilate

```bash
cd hw/verilator_model/

# Compile `libpspin.so`
make release

# (Optional) Compile `libpspin_debug.so`
make debug
```


