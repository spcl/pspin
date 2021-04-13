#!/bin/bash


num_packets=$1
spin_app_name=$2
handlers_prefix=$3
pkt_length=$4
pkt_delay=$5
msg_delay=$6
full_pkt=$7
num_msgs=$8
pktgen_bin=$9
pktgen_params=${10}
has_hh=${11}
has_th=${12}
pkt_seed=${13}
custom_hdr_size=${14}

echo "CUSTOM HDR SIZE: $custom_hdr_size"
if [ ! -f "$pktgen_bin" ]; then
    echo "Generic packet generator not found! Please build $pktgen_bin!"
    exit 1
fi
echo $pktgen_params

$pktgen_bin --msg-count=$num_msgs --count=$num_packets --pkt-length=$pkt_length --binary="build/$spin_app_name" --handler-prefix="$handlers_prefix" --pkt-delay=$pkt_delay --msg-delay=$msg_delay --full-pkt=$full_pkt --has-hh=$has_hh --has-th=$has_th --target-dir=$PSPIN_HW/sim_files/ --seed=$pkt_seed --custom-hdr=$custom_hdr_size ${pktgen_params} 

