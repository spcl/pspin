#!/bin/bash

trace="$1";
key="$2";
cfiles="$3";

clines=$(grep -nH "TELEMETRY" $cfiles | sed "s/\(.*\):\([0-9]*\):.*TELEMETRY:[ ]*\([^;]*\).*/\1 \2 \3/g");
IFS=$'\n';


clean_trace=""

for cline in $clines; do
    IFS=$' ';
    cline_array=($cline);

    file_start=$(basename "${cline_array[0]}");
    line_start="${cline_array[1]}";
    label="${cline_array[2]}";
    label_name=$label

    if [[ $label == *":START"* ]]; then
        label_name=${label/\:START/};
        label_end="$label_name END";

        cline_end=$(echo "$clines" | grep "$label_name:END");
        cline_end_array=($cline_end);
        file_end=$(basename "${cline_end_array[0]}");
        line_end="${cline_end_array[1]}";
        
    elif [[ $label == *":END"* ]]; then
        continue;
    else
        file_end=$file_start
        line_end=$line_start
    fi;

    echo "#$label start: $file_start:$line_start; end: $file_end:$line_end"
    core_ids="$(cat $trace | grep "${file_start}:${line_start}" | cut -d " " -f 4,5 | uniq)";       



    IFS=$'\n';
    for core_id in $core_ids; do
        IFS=$' ';

        #echo "core_id: $core_id"   

        cat $trace | grep " $core_id " | 
        awk -v start="$file_start:$line_start" -v end="$file_end:$line_end" -v label="$label_name" -v core_id="$core_id" -v key="$key" \
        'BEGIN{count=0; counting=0; start_time=0;}
         {
            if ($8==start && $9=="nop" && counting==0){ 
                counting=1;
                start_time=$1;
                loads=0;
                stores=0;
                branches=0;
                bsws=0;
                l2_accesses=0;
                handler="none";
                next;
            }

            if (counting==1) { 

                if ($9~/lw|lb|lh/) loads = loads + 1;

                if ($0~/PA:1c/) l2_accesses = l2_accesses + 1;

                if ($9=="bsw") bsws = bsws + 1;
                else if ($9~/sw|sb|sh/) stores = stores + 1;
                
                if ($9~/beq|bne|blt|bge/) branches = branches + 1;

                if ($6~/_ph$|_hh$|_th$/) handler=$6;

                count = count+1; 
            }

            

            if ($8==end && $9=="nop") { 
                counting=0; 
                end_time=$1
                latency=end_time - start_time;
                print key " " label " " handler " " core_id " " start_time " " end_time " " latency " " count " " loads " " stores " " bsws " " branches " " l2_accesses;
                count=0;

                if ($8 == start) {
                    counting=1;
                    start_time=$1;
                    loads=0;
                    stores=0;
                    branches=0;
                    bsws=0;
                    l2_accesses=0;
                    handler="none";
                }

            }

         }'
    done
done;

    


