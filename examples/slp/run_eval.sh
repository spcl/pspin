#!/usr/bin/env bash

EXEC=./sim_slp_l1
TRACEVIS=$HOME/work/pspin/sw/scripts/tracevis/parse.pl
OUT_DATA=$PWD/data/

mkdir -p $OUT_DATA

dtype_candidates="int8_t int16_t int32_t float"
vlen_candidates="8 16 32 64 128"
mode_candidates="predict fit"
p_candidates="8 16 32 64 128 256 512 1024"
s_candidates="128 256 512 1024"
p_cutoff=256

die() {
    echo "$@"
    exit 1
}

# https://unix.stackexchange.com/a/216475/141443
open_sem() {
    mkfifo pipe-$$
    exec 3<>pipe-$$
    rm pipe-$$
    local i=$1
    for ((; i>0; i--)); do
        printf %s 000 >&3
    done
}

run_with_lock() {
    local x
    read -u 3 -n 3 x && ((0==x)) || die "Job failed with code $x: $@"
    (
        ( "$@"; )
        printf '%.3d' $? >&3
    )&
}

N=$(nproc)
open_sem $N

build() {
    make all DTYPE=$1 VLEN=$2 || die "Build failed for DTYPE=$1 VLEN=$2"
    mkdir -p eval-$2-$1
    mv build sim_slp_l1 eval-$2-$1
}

run() {
    if [[ $3 -gt $p_cutoff && $5 == "fit" ]]; then
        return 0 # cutoff
    fi
    trial_name=eval-$2-$1-p$3-s$4-$5
    cp -R eval-$2-$1 $trial_name
    pushd $trial_name
    echo ">>> Evaluating $1 $2 p=$3 s=$4 $5"
    if [[ $5 == "predict" ]]; then
        export PREDICT_ONLY=1
    fi
    $PWD/$EXEC -m 1 -p $3 -s $4 &> $OUT_DATA/$trial_name.transcript.txt || return 2
    perl $TRACEVIS build/slp_l1 ./trace_core_* > $OUT_DATA/$trial_name.json || return 3
    unset PREDICT_ONLY
    popd
    rm -rf $trial_name
    echo "<<< Finished $1 $2 p=$3 s=$4 $5"
}

source ../../sourceme.sh

for dt in $dtype_candidates; do
    for vl in $vlen_candidates; do
        build $dt $vl
        for p in $p_candidates; do
            for s in $s_candidates; do
                for m in $mode_candidates; do
                    run_with_lock run $dt $vl $p $s $m
                done
            done
        done
    done
done

wait
echo 'All done!'
