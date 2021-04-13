# tracevis

**Requires:**  perl >= v5.26; addr2line >= 2.30. Could work with lower versions too, but it is not tested.

**Usage:**
```perl ./parse.pl [-i] [-p] <binary> <trace file 1> ... <trace file n>```

The trace files are expected to be the ones produced by RI5CY cores in RTL simulation (default) or GVSOC virtual platform (with `-g` flag).

**Output:** JSON that can be loaded into chrome tracing (about://tracing from chrome or chromium)

**Options:**
  - ```-i```: inlines instructions. Even if a function is inlined, it is still possible to see the inlined function. By default we show
 the origin function name, even if it inlined. If this option is specified the instructions are shown as belonging to the inlining function.
  - ```-p```: labels the instruction with the PC instead of the instruction type. 
  - ```-g```: parses traces produced by GVSOC running with `--trace=/sys--trace=/sys/board/chip/cluster/pe0:pe0.log` (or similar for other cores).

**Example:**
The example/ folder contains: 
 - bin/pulp_api_example: a sample binary;
 - traces/trace*.log: the per-core RI5CY traces produced by the RTL simulation of the above binary file;
 - chrome.json: the output file produced by the script when the above binary and traces are given as input.

The chrome.json can be produced by running the following command:
```
perl parse.pl example/bin/pulp_api_example example/traces/trace_core_0*.log > chrome.json
```

**Known Limitations:**
The tracer embedded in Google Chrome (`chrome://tracing`) is not able to open very large traces.
Empirically we saw that up to ~500k events can be managed. Things that can help:
 - Gzipping the trace
 - Slicing the JSON trace in https://github.com/facebook/buck/blob/d609be052ddd49a746e185fadf6df08cc19af6d2/scripts/slice_trace.py
 - Try switching to Catapult Trace-Viewer: https://chromium.googlesource.com/catapult/+/HEAD/tracing/README.md. It will compile the json trace to a HTML page (still requires a chromium-based browser to open it).
   ```
   $CATAPULT/tracing/bin/trace2html my_trace.json --output=my_trace.html && open my_trace.html
   ```
 - Using another visualizer?
