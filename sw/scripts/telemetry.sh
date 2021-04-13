#/bin/bash

binary=$1
traces_dir=$2
key="$3"
cfiles="$4"
traces="trace_core_*.log"

echo "#" > data.telemetry.time
echo -n "#" > data.telemetry.instr
key=${key/,/ }
echo "key: $key"
gdb_regex='s/.*0x\([a-f0-9]\+\).*0x.*/\1/'
trace_regex='s/\(.*\):[0-9]*:[ ]*[0-9]*[ ]*\([0-9]*\).*/\1 \2/g'
lines=$(grep -nH "TELEMETRY" $cfiles | sed "s/\(.*\):\([0-9]*\):.*TELEMETRY:[ ]*\([^;]*\).*/\1 \2 \3/g");
echo $cfiles
echo $lines
IFS=$'\n' 
for line in $lines; do
    IFS=$' ' 
    linearr=($line);
    IFS=$'\n' 

    file=${linearr[0]}
    line=${linearr[1]}
    label=${linearr[2]}
    
    pc=$(gdb $binary -ex "info line ${file}:${line}" --batch | sed "$gdb_regex")
    grep -n "\s*[0-9]*\s[0-9]*\s${pc}.*" $traces | sed "$trace_regex" | awk -v pc="$pc" -v label="$label" -v key="$key" 'NR==1{old=$2;}{diff=$2-old; print key " " label " " $1 " " pc " " $2 " " diff; old=$2;}' >> data.telemetry.time

    if [[ $label == *":STOP"* ]]; then
        #echo "skipping STOP range label"
        continue;  
    fi

    echo "# LABEL: $label; FILE: $file; LINE: $line; PC: $pc"
    #continue;

    if [[ $label == *":START"* ]]; then
        stop_label=${label/START/STOP};
        label_name=${label/\:START/};

        stop_label_code=($(grep -n "TELEMETRY: $stop_label" $PSPIN_RT/src/*.c | sed "s/\(.*\):\([0-9]*\):.*TELEMETRY:[ ]*\([^;]*\).*/\1 \2 \3/g"));

        IFS=$' ' 
        stop_label_code=($stop_label_code)
        IFS=$'\n' 

        stop_label_file=${stop_label_code[0]}
        stop_label_line=${stop_label_code[1]}

        stop_label_pc=$(gdb $binary -ex "info line ${stop_label_file}:${stop_label_line}" --batch | sed "$gdb_regex")
        echo " --> THIS IS A RANGE LABEL: $label_name! Stop label: $stop_label; file: $stop_label_file; line: $stop_label_line; pc: $stop_label_pc"

        files=$(grep -r "$pc" $traces | sed "s/\([^:]\):.*/\1/g" | uniq)
        for file in $(ls $files); do
            cat $file | awk -v pc_start="$pc" -v pc_stop="$stop_label_pc" -v label_name="$label_name" -v f="$file" -v key="$key" 'NR==1{printf " 0"; next;}NR==2{id=-1; old=$2; pid=id;}{diff=$2-old; if ($3==pc_start) {id=id+1; pid=id}; if ($3==pc_stop) {pid=-1;} printf " " diff "\n" key " " f " " label_name " " pid " " $2 " " $3 " " $5; old=$2}' >> data.telemetry.instr
            echo -n -e " 0\n#" >> data.telemetry.instr
            #the last ID should be removed from the analysis. The last instruction of the last ID has time 0.
            #the ID -1 are the instr before the first appearance of the selected PC. 
        done;

    else

        files=$(grep -r "$pc" $traces | sed "s/\([^:]\):.*/\1/g" | uniq)
        for file in $(ls $files); do
            cat $file | awk -v pc="$pc" -v label="$label" -v f="$file" -v key="$key"  'NR==1{printf " 0"; next;}NR==2{id=-1; old=$2;}{diff=$2-old; if ($3==pc) {id=id+1;}; printf " " diff "\n" key " " f " " label " " id " " $2 " " $3 " " $5; old=$2}' >> data.telemetry.instr
            echo -n -e " 0\n#" >> data.telemetry.instr
            #the last ID should be removed from the analysis. The last instruction of the last ID has time 0.
            #the ID -1 are the instr before the first appearance of the selected PC. 
        done;
    fi;
done;
