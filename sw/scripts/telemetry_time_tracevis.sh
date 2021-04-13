#!/bin/bash

trace="$1";
key="$2";
cfiles="$3";

clines=$(grep -nH "TELEMETRY" $cfiles | sed "s/\(.*\):\([0-9]*\):.*TELEMETRY:[ ]*\([^;]*\).*/\1 \2 \3/g");
IFS=$'\n';


for cline in $clines; do
    IFS=$' ';
    cline_array=($cline);

    file=$(basename "${cline_array[0]}");
    line="${cline_array[1]}";
    label="${cline_array[2]}";

    echo "#file: $file; line: $line; label: $label";
    
    if [[ $label == *":START"* ]]; then
        label_name=${label/\:START/};
        label="$label_name START";

    elif [[ $label == *":END"* ]]; then
        label_name=${label/\:END/};
        label="$label_name END";
    else 
        label="$label SINGLE"
    fi;

    trace_lines=$(cat $trace | grep "${file}:$line" | sed "s/\(.*\)/$key $label \1/g");
 
    echo $trace_lines
   
    IFS=$'\n';
done


