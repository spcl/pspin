# Running examples

### Compile handlers and simulation driver and run! 
Here we show how to compile&run the `ping-pong` example. Same instructions apply for other examples too. 

```bash
cd examples/ping_pong
make all
```

This prouduces two executable: `sim_pingpong` (linked against `libpspin.so`) and `sim_pingpong_debug` (linked against `libpspin_debug.so`). Type `./sim_pingpong --help` to see the possible command-line arguments or just run `./sim_pingpong` to run with the default arguments.


### Check data

The simulation produces a summary at the end that looks like this:
```
###### Statistics ######
NIC inbound engine:
	Packets: 32; Bytes: 32768
	Avg packet length: 1024.000 B
	Feedback throughput: 443.197 Gbit/s (feedback arrival time: 18.484 ns)
	Packet latency: avg: 119.750 ns; min: 108 ns; max: 155 ns
	HER stalls: 0
----------------------------------
NIC outbound engine:
	Commands: 32; Packets: 32; Bytes: 32768
	Avg packet length: 1024.000 B
	Packet throughput: 443.197 Gbit/s (pkt departure time: 18.484 ns)
----------------------------------
PCIe Slave:
	Writes: beats: 0; bytes: 0; avg throughput: -nan Gbit/s
	Reads: beats: 0; bytes: 0; avg throughput: -nan Gbit/s
----------------------------------
PCIe Master:
	Bytes written: 0; Bytes read: 0
----------------------------------
```

It reports information for each of the functional modules (i.e., NIC inbound and outbound engines, PCIe). 

To gain more insights, you can type: `make info` to produce information about the executed handlers:
```
#[key] handler cluster_id core_id start_time end_time latency instructions loads stores bsws branches l2_accesses local_l1_accesses remote_l1_accesses other_accesses
 pingpong_ph 00 0 1225000 1312000 87000 29 9 10 0 0 0 11 0 8
 pingpong_ph 00 0 1325000 1363000 38000 29 9 10 0 0 0 11 0 8
 pingpong_ph 00 0 1385000 1423000 38000 29 9 10 0 0 0 11 0 8
 pingpong_ph 00 0 1445000 1483000 38000 29 9 10 0 0 0 11 0 8
...
```
In particular, it shows for each executed handler, the cluster and core where it has been executed, the starting and ending times (in picoseconds), the duration (in picoseconds), total number of instructions, and number of instructions per instruction class.

We also provide a tool for quick&raw data visualization: `make stats` (note: needs gnuplot installed). It works only if you redirected the simulation stdout to a `transcript` file (e.g., `./sim_pingpong > transcript`).

### Debugging 

In order to debug the handlers, you can produce a trace of all executed instructions with `make trace`. The output reports one instruction per line:
```
1845000 1841 1000 00 1 pingpong_ph 1d0003b2 ping_pong.c:38 lhu "lhu  x12, 2(x14)         x12=00000400 x14:1000bc00  PA:1000bc02"
```
It reports the following information:
 - time at which the instruction completed (picoseconds): `1845000`
 - time at which the instruction completed (cycles): `1845`
 - duration (picoseconds): `1000`
 - cluster ID from where the instruction originated: `00`
 - core ID (relative to the cluster) from where the instruction originated: `1`
 - function name: `pingpong_ph`
 - program counter: `1d0003b2`
 - file:line: `ping_pong.c:38`
 - instruction mnemonic: `lhu`
 - full instruction with actual register values: `lhu  x12, 2(x14)         x12=00000400 x14:1000bc00  PA:1000bc02`

Alternatively, you produce JSON trace with `make trace-chrome` and visualize them with your browser (type `about://tracing` in the address bar and load the JSON file). Works on Google Chrome, Chromimum, and Firefox. 

<div align="center"><img src="https://github.com/spcl/pspin/raw/master/docs/trace_example.png" alt="Visualizing execution traces" /></div>

Note: the tracing tool is available at https://github.com/SalvatoreDiGirolamo/tracevis and can be used to produce enriched traces from RI5CY traces.

