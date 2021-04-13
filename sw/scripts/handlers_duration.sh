#!/bin/bash

cat $1 | grep INFO | grep "HANDLER_START\|HPU_TIME" | cut -f 1-5 -d " " | sed "s/\[\([0-9]*\)\]\[.*\]:\(.*\)/\1\2/g" | sort -k 1 -n | sort -k 4,5 -s | awk '{if (NR % 2) {prev=$1} else {diff=$1-prev; starttime=prev; prev=$1; print $1 " " $4 " " $5 " " $4 $5 " " diff " " starttime;}}' > data.tmp


cat $1 | grep INFO | grep "HANDLER_START\|HPU_TIME" | cut -f 1-5 -d " " | sed "s/\[\([0-9]*\)\]\[.*\]:\(.*\)/\1\2/g" | sort -k 1 -n | sort -k 4,5 -s | awk 'BEGIN {max=0; min=0; sum=0; count=0;} {if (NR % 2) {prev=$1} else {diff=$1-prev; starttime=prev; prev=$1; sum+=diff; count++; if (NR==2) { max=diff; min=diff; } else { max = (max>diff) ? max : diff; min = (min<diff) ? min : diff;}}} END{ avg = sum/(count); print "Total handlers: " count "; Handler runtime (ns): avg: " avg/1000 "; min: " min/1000 "; max: " max/1000 }'


#cat data.tmp


gnuplot -e "set style data histogram; set style histogram cluster gap 1; set term dumb 150 40; binwidth = 100; bin(x, width) = width*floor(x/width)/1000; set tics out nomirror; plot 'data.tmp' using (bin(\$5, binwidth)):(1.0) smooth freq with boxes"


echo -e "\n\n#### Handlers running time: x: sim time (ns); y: handler time (ns) ####"
gnuplot -e "set term dumb 150 40; plot 'data.tmp' using (\$6/1000):(\$5/1000) w p"

#gnuplot -e "set term dumb 100 40; plot 'data.tmp' using (\$6/1000):4 w p"

echo -e "\n\n#### Handlers distribution: x: sim time (ns); y: hpu id (cluster_id * 10 + core_id). A: start time; B: finish time (B not shown if too close to next A) ####"
gnuplot -e "set term dumb 150 45; set yrange [-1:38]; plot 'data.tmp' using (\$6/1000):4 w p, 'data.tmp' using (\$1/1000):4 w p, 8 title '', 18 title '', 28 title ''"
