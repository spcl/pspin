#!/bin/bash

#15067000 15063 1000 00 0 spin_host_write 1d000426 handler.h:267 add "add  x13, x13, x0        x13=00000000 x13:00000000"

key=$1
trace_file=$2
#pc_handler_start=$2
#pc_handler_end=$3

cfile=$PSPIN_RT/runtime/src/hpu.c

hstart_line=$(grep -nH "TELEMETRY: HANDLER:START" $cfile)
hstop_line=$(grep -nH "TELEMETRY: HANDLER:END" $cfile)

old_ifs=$IFS
IFS=$':';

hstart_line_array=($hstart_line);
hstart_linenum="${hstart_line_array[1]}";

hstop_line_array=($hstop_line);
hstop_linenum="${hstop_line_array[1]}";

IFS=$old_ifs

cfile=$(basename $cfile)
hstart_coord="$cfile:$hstart_linenum"
hstop_coord="$cfile:$hstop_linenum"

echo "#START: $hstart_coord; END: $hstop_coord"

echo "#[key] handler cluster_id core_id start_time end_time latency instructions loads stores bsws branches l2_accesses local_l1_accesses remote_l1_accesses other_accesses"

for cluster_id in 00 01 02 03; do
    for hpu_id in 0 1 2 3 4 5 6 7; do

        trace=$(cat $trace_file | grep " $cluster_id $hpu_id ")
            
        echo "$trace" | gawk -v start="$hstart_coord" -v end="$hstop_coord" -v core_id="$hpu_id" -v cluster_id="$cluster_id" -v key="$key" \
        'BEGIN{count=0; counting=0; start_time=0; new_handler=0;}
         {
            if ($8==start) {
                counting=1;
                #start_time=$1;
                loads=0;
                stores=0;
                branches=0;
                bsws=0;
                l2_accesses=0;
                local_l1_accesses=0;
                remote_l1_accesses = 0;
                other_accesses = 0;
                handler="none";
                new_handler=1;
                next;
            }
    
            if (new_handler==1) {
                start_time=$1;
                new_handler=0;
            }

            if (counting==1) { 

                if ($9~/lw|lb|lh/) loads = loads + 1;

                is_mem_access = match($0, /PA:([0-9a-fA-F]+)/, addr_match); 
                if (is_mem_access) {

                    #remote vs local accesses
                    if ($0~/PA:1c/) l2_accesses = l2_accesses + 1;
                    else {

                        addr = strtonum("0x" addr_match[1]);
                        #print addr_match[1];
                        addr_cluster_target = -1;
                        if (addr >= 0x10000000 && addr < 0x10400000) addr_cluster_target = 0;
                        else if (addr >= 0x10400000 && addr < 0x10800000) addr_cluster_target = 1;
                        else if (addr >= 0x10800000 && addr < 0x10c00000) addr_cluster_target = 2;
                        else if (addr >= 0x10c00000 && addr < 0x11000000) addr_cluster_target = 3;
    
                        if (addr_cluster_target == int($4)) local_l1_accesses = local_l1_accesses + 1;
                        else if (addr_cluster_target != -1) remote_l1_accesses = remote_l1_accesses + 1;
                        else {
                            #print "other access: " addr_match[1];
                            other_accesses = other_accesses + 1;
                        }
                    }
                }


                if ($9=="bsw") bsws = bsws + 1;
                else if ($9~/sw|sb|sh/) stores = stores + 1;
                
                if ($9~/beq|bne|blt|bge/) branches = branches + 1;

                if ($6~/_ph$|_hh$|_th$/) handler=$6;

                count = count+1; 
            }

            if ($8==end) { 
                counting=0; 
                end_time=$1
                latency=end_time - start_time;
                print key " " handler " " cluster_id " " core_id " " start_time " " end_time " " latency " " count " " loads " " stores " " bsws " " branches " " l2_accesses " " local_l1_accesses " " remote_l1_accesses " " other_accesses;
                count=0;
            }
         }'
    done
done

