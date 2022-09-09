#!/bin/bash

# Prios
PRIOS="0=1024;1=1024;2=512;3=1;4=1024;10=1"

SCHEDULER="RR"
echo "Running $SCHEDULER PRIOS: $PRIOS"
FMQ_ARBITER_TYPE="$SCHEDULER" PRIO_OVERRIDE="$PRIOS" ./sim_empty > transcript
OUTDIR="data/scripted/multiflow/$SCHEDULER/"
cat transcript | grep "INFO FEEDBACK" | sed "s/[][]/ /g" | sed "s/\://g" | sed "s/[ ]\+/ /g" > out.data
cat transcript | grep idx | sed "s/[a-z_]\+=//g" | sed "s/;//g" > queues
make trace
mkdir -p $OUTDIR
mv empty.trace.txt transcript out.data queues $OUTDIR

SCHEDULER="PRIO"
echo "Running $SCHEDULER PRIOS: $PRIOS"
FMQ_ARBITER_TYPE="$SCHEDULER" PRIO_OVERRIDE="$PRIOS" ./sim_empty > transcript
OUTDIR="data/scripted/multiflow/$SCHEDULER/"
cat transcript | grep "INFO FEEDBACK" | sed "s/[][]/ /g" | sed "s/\://g" | sed "s/[ ]\+/ /g" > out.data
cat transcript | grep idx | sed "s/[a-z_]\+=//g" | sed "s/;//g" > queues
make trace
mkdir -p $OUTDIR
mv empty.trace.txt transcript out.data queues $OUTDIR

SCHEDULER="PRIO-FAIR-STRICT"
echo "Running $SCHEDULER PRIOS: $PRIOS"
FMQ_ARBITER_TYPE="$SCHEDULER" PRIO_OVERRIDE="$PRIOS" ./sim_empty > transcript
OUTDIR="data/scripted/multiflow/$SCHEDULER/"
cat transcript | grep "INFO FEEDBACK" | sed "s/[][]/ /g" | sed "s/\://g" | sed "s/[ ]\+/ /g" > out.data
cat transcript | grep idx | sed "s/[a-z_]\+=//g" | sed "s/;//g" > queues
make trace
mkdir -p $OUTDIR
mv empty.trace.txt transcript out.data queues $OUTDIR

SCHEDULER="PRIO-FAIR-DYN"
echo "Running $SCHEDULER PRIOS: $PRIOS"
FMQ_ARBITER_TYPE="$SCHEDULER" PRIO_OVERRIDE="$PRIOS" ./sim_empty > transcript
OUTDIR="data/scripted/multiflow/$SCHEDULER/"
cat transcript | grep "INFO FEEDBACK" | sed "s/[][]/ /g" | sed "s/\://g" | sed "s/[ ]\+/ /g" > out.data
cat transcript | grep idx | sed "s/[a-z_]\+=//g" | sed "s/;//g" > queues
make trace
mkdir -p $OUTDIR
mv empty.trace.txt transcript out.data queues $OUTDIR

