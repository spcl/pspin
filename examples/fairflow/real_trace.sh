#/bin/bash

PRIOS="1=1024;2=1024;3=512;4=10;5=10;6=10"

SCHEDULER="PRIO-FAIR-DYN"
echo "Running $SCHEDULER PRIOS: $PRIOS"
FMQ_ARBITER_TYPE="$SCHEDULER" PRIO_OVERRIDE="$PRIOS" ./sim_empty | tee transcript
OUTDIR="data/scripted/real/$SCHEDULER/"
cat transcript | grep "INFO FEEDBACK" | sed "s/[][]/ /g" | sed "s/\://g" | sed "s/[ ]\+/ /g" > out.data
cat transcript | grep idx | sed "s/[a-z_]\+=//g" | sed "s/;//g" > queues
make trace
mkdir -p $OUTDIR
mv empty.trace.txt transcript out.data queues $OUTDIR


