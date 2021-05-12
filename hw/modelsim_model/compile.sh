#!/usr/bin/env bash

set -e

#make -C .. vsim/compile.tcl

vsim -c -do 'source compile.tcl; quit'

