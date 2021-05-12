vsim -voptargs="+acc" -t 1ps -warning 3009 pspin_tb
set StdArithNoWarnings 1
set NumericStdNoWarnings 1

log -r /*

#source ../test/pspin_tb.wave.do

run -a