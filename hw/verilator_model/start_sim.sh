#/bin/bash

sim=pspin_release

if [ "$1" -eq "1" ]; then
    sim=pspin_debug
fi

stdbuf -oL ${PSPIN_HW}/${PSPIN_SIM}/bin/$sim | tee transcript
