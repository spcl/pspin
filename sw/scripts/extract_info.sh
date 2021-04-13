#!/bin/bash

info_key=$1
transcript_file=$2

info_key_parsed=$(echo $info_key | sed "s/,/ /g")

#cat $transcript_file | grep INFO | cut -d " " -f 2-4 | sed "s/\(.*\)/$info_key_parsed \1/g"


cat $transcript_file | grep INFO | sed "s/\[\([0-9]*\)\]\[.*\]: INFO \([^ ]*\) .*/$info_key_parsed \2 \1/g"
