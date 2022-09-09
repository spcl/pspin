#!/bin/bash

# Prios
PRIOS="0=1024;1=1024;2=512;3=1;4=1024;10=1"

#SCHEDULER="PRIO-FAIR-DYN"
#FLOW_FILTER="1;2;3;10"
#echo "Running $SCHEDULER PRIOS: $PRIOS FILTER: $FLOW_FILTER"
#NI_FLOW_FILTER="$FLOW_FILTER" FMQ_ARBITER_TYPE="$SCHEDULER" PRIO_OVERRIDE="$PRIOS" ./sim_empty > transcript
#OUTDIR="data/scripted/isolation/${SCHEDULER}_F0/"
#cat transcript | grep "INFO FEEDBACK" | sed "s/[][]/ /g" | sed "s/\://g" | sed "s/[ ]\+/ /g" > out.data
#cat transcript | grep idx | sed "s/[a-z_]\+=//g" | sed "s/;//g" > queues
#make trace
#mkdir -p $OUTDIR
#mv empty.trace.txt transcript out.data queues $OUTDIR

SCHEDULER="PRIO-FAIR-DYN"
FLOW_FILTER="0;2;3;4;10"
echo "Running $SCHEDULER PRIOS: $PRIOS FILTER: $FLOW_FILTER"
NI_FLOW_FILTER="$FLOW_FILTER" FMQ_ARBITER_TYPE="$SCHEDULER" PRIO_OVERRIDE="$PRIOS" ./sim_empty > transcript
OUTDIR="data/scripted/isolation/${SCHEDULER}_F1/"
cat transcript | grep "INFO FEEDBACK" | sed "s/[][]/ /g" | sed "s/\://g" | sed "s/[ ]\+/ /g" > out.data
cat transcript | grep idx | sed "s/[a-z_]\+=//g" | sed "s/;//g" > queues
make trace
mkdir -p $OUTDIR
mv empty.trace.txt transcript out.data queues $OUTDIR


SCHEDULER="PRIO-FAIR-DYN"
FLOW_FILTER="0;1;3;4;10"
echo "Running $SCHEDULER PRIOS: $PRIOS FILTER: $FLOW_FILTER"
NI_FLOW_FILTER="$FLOW_FILTER" FMQ_ARBITER_TYPE="$SCHEDULER" PRIO_OVERRIDE="$PRIOS" ./sim_empty > transcript
OUTDIR="data/scripted/isolation/${SCHEDULER}_F2/"
cat transcript | grep "INFO FEEDBACK" | sed "s/[][]/ /g" | sed "s/\://g" | sed "s/[ ]\+/ /g" > out.data
cat transcript | grep idx | sed "s/[a-z_]\+=//g" | sed "s/;//g" > queues
make trace
mkdir -p $OUTDIR
mv empty.trace.txt transcript out.data queues $OUTDIR


SCHEDULER="PRIO-FAIR-DYN"
FLOW_FILTER="0;1;2;4;10"
echo "Running $SCHEDULER PRIOS: $PRIOS FILTER: $FLOW_FILTER"
NI_FLOW_FILTER="$FLOW_FILTER" FMQ_ARBITER_TYPE="$SCHEDULER" PRIO_OVERRIDE="$PRIOS" ./sim_empty > transcript
OUTDIR="data/scripted/isolation/${SCHEDULER}_F3/"
cat transcript | grep "INFO FEEDBACK" | sed "s/[][]/ /g" | sed "s/\://g" | sed "s/[ ]\+/ /g" > out.data
cat transcript | grep idx | sed "s/[a-z_]\+=//g" | sed "s/;//g" > queues
make trace
mkdir -p $OUTDIR
mv empty.trace.txt transcript out.data queues $OUTDIR

