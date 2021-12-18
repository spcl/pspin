#!/usr/bin/env bash

EXEC=./sim_slp_l1
TRACE_FILENAME=slp_l1.trace.json

p_candidates="8 16 32 64"
s_candidates="128 256 512 1024"

if [[ $# != 1 ]]; then
    echo "usage: $0 <out_dir>"
    exit 1
fi

make all || exit 1

DATA_DIR=$1
mkdir -p $DATA_DIR

for p in $p_candidates; do
    for s in $s_candidates; do
        echo ">>>>>>>> Evaluating p=$p s=$s <<<<<<<<"

        rm $TRACE_FILENAME *.log
        $EXEC -m 1 -p $p -s $s &> $DATA_DIR/fit_p${p}s${s}.transcript.txt
        make trace-chrome
        mv $TRACE_FILENAME $DATA_DIR/fit_p${p}s${s}.json

        rm $TRACE_FILENAME *.log
        PREDICT_ONLY=1 $EXEC -m 1 -p $p -s $s &> $DATA_DIR/predict_p${p}s${s}.transcript.txt
        make trace-chrome
        mv $TRACE_FILENAME $DATA_DIR/predict_p${p}s${s}.json
    done
done
