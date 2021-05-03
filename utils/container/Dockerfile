# Copyright (C) 2020 ETH Zurich
# 
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# 
#     https://www.apache.org/licenses/LICENSE-2.0
# 
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

FROM ubuntu:18.04 as build-hw
WORKDIR /tools
ARG VERILATOR_VERSION=4.202

SHELL ["/bin/bash", "-c"]

RUN apt-get update --assume-yes && \
    apt-get install --assume-yes \
    wget curl gnupg gnupg2 git build-essential python gengetopt libncurses5 gawk

# Get Verilator
RUN wget http://spclstorage.inf.ethz.ch/~digirols/pspin/verilator-${VERILATOR_VERSION}.tar && \
    tar -xvf verilator-${VERILATOR_VERSION}.tar
ENV PATH="/tools/verilator/bin/:${PATH}"
ENV VERILATOR_ROOT="/tools/verilator/"

# Get RISCV-GCC toolchain
RUN wget spclstorage.inf.ethz.ch/~digirols/pspin/riscv-gcc-ubuntu.tar.gz > /dev/null && \
    tar -xvf /tools/riscv-gcc-ubuntu.tar.gz -C /tools && \
    chmod 777 -R /tools/riscv-gcc/ && \
    rm /tools/riscv-gcc-ubuntu.tar.gz

# Get clang-9
RUN curl -SL http://releases.llvm.org/9.0.0/clang+llvm-9.0.0-x86_64-linux-gnu-ubuntu-18.04.tar.xz | tar -xJC . \
    && mv clang+llvm-9.0.0-x86_64-linux-gnu-ubuntu-18.04 clang_9.0.0
ENV PATH="/tools/clang_9.0.0/bin:/usr/bin/cmake/bin:${PATH}"
ENV LD_LIBRARY_PATH="/tools/clang_9.0.0/lib:${LD_LIBRARY_PATH}"
 
WORKDIR /home/

# Get repo and configure paths
RUN git clone https://github.com/spcl/pspin.git && \
    cd pspin && \
    cat sourceme-template.sh | \ 
    sed "s%RISCV_GCC=%RISCV_GCC=/tools/riscv-gcc/bin/%g" | \
    sed "s%PSPIN_HW=%PSPIN_HW=/home/pspin/hw/%g" | \
    sed "s%PSPIN_RT=%PSPIN_RT=/home/pspin/sw%g" > sourceme.sh
 
# Verilate
RUN export VERILATOR_HOME=/usr/share/verilator/ && \
    cd pspin/hw/verilator_model/ && \
    VERILATOR_COMPILER_WORKERS=2 make release

# Test
RUN source pspin/sourceme.sh && \
    cd pspin/examples/empty && \
    make deploy && \
    make driver && \
    make run
