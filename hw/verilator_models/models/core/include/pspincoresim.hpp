// Copyright 2020 ETH Zurich
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#pragma once

#include <stdint.h>
#include <stdlib.h>
#include <functional>

#include "Vpspin_verilator.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "DMAEngine.hpp"
#include "DMATarget.hpp"
#include "NOSlave.hpp"
#include "NIMaster.hpp"
#include "SimControl.hpp"
#include "pspin.hpp"

namespace PsPIN 
{

class PsPINCoreSim {

public:
    typedef NOSlave::NICCommand NICCommand;
    typedef NOSlave::NICCommandCallback NICCommandCallback;
    typedef NIMaster::HERCompletetionCallback HERCompletetionCallback;
    typedef DMAEngine<AXIPort<uint32_t, uint64_t>>::mst_write_cb_t WriteCompletedCallback;
    typedef DMAEngine<AXIPort<uint32_t, uint64_t>>::mst_read_cb_t ReadCompletedCallback;
    typedef DMATarget<AXIPort<uint64_t, uint64_t>>::slv_write_cb_t HostWriteCallback;
    typedef DMATarget<AXIPort<uint64_t, uint64_t>>::slv_read_cb_t HostReadCallback;

public:
    PsPINCoreSim(std::string vcd_file_path);

    // NIC -> PsPIN memory
    void setNICWriteBufferSize(uint32_t size) { ni_data_mst->set_write_buff_size(size); }
    void setNICReadBufferSize(uint32_t size) { no_data_mst->set_read_buff_size(size); }
    bool canNICWrite() { return ni_data_mst->can_write(); }
    bool canNICRead() { return no_data_mst->can_read(); }
    int nicMemWrite(uint32_t addr, uint8_t *data, size_t size, WriteCompletedCallback cb);
    int nicMemRead(uint32_t addr, uint8_t *data, size_t size, ReadCompletedCallback cb);

    // Host -> PsPIN memory
    void setHostWriteBufferSize(uint32_t size) { host_data_mst->set_write_buff_size(size); }
    void setHostReadBufferSize(uint32_t size) { host_data_mst->set_read_buff_size(size); }
    bool canHostWrite() { return host_data_mst->can_write(); }
    bool canHostRead() { return host_data_mst->can_read(); }
    int hostMemWrite(uint32_t addr, uint8_t *data, size_t size, WriteCompletedCallback cb);
    int hostMemRead(uint32_t addr, uint8_t *data, size_t size, ReadCompletedCallback cb);

    // NIC -> PsPIN (new HER)
    void setHERBufferSize(uint32_t size) { ni_ctrl_mst->set_her_buffer_size(size); }
    bool canSendHER() { return ni_ctrl_mst->can_send_her(); };
    int sendHER(her_descr_t *her, HERCompletetionCallback cb);

    // PsPIN -> NIC outbound
    bool setNICCommandStatus(bool blocked);
    int setNICCommandCallback(NICCommandCallback cb);

    // PsPIN -> Host
    bool setHostWriteStatus(bool blocked);
    int setHostWriteCallback(HostWriteCallback cb);

    bool setHostReadStatus(bool blocked);
    int setHostReadCallback(HostReadCallback cb);

    // Simulation control
    int run();
    int step(uint8_t *done_flag);
    int shutdown();

    // Stats
    void printStats();

    ~PsPINCoreSim()
    {
        delete sim;
        delete host_data_slv;
        delete host_data_mst;
        delete ni_data_mst;
        delete no_data_mst;
        delete ni_ctrl_mst;
        delete no_ctrl_slv;
    }

private:
    AXIPort<uint32_t, uint64_t>                 ni_data_mst_port;
    ni_control_port_t                           ni_ctrl_mst_port;
    AXIPort<uint32_t, uint64_t>                 no_data_mst_port;
    no_cmd_port_t                               no_ctrl_slv_port;
    AXIPort<uint64_t, uint64_t>                 host_slv_port;
    AXIPort<uint32_t, uint64_t>                 host_mst_port;

    SimControl<Vpspin_verilator>*               sim;
    DMATarget<AXIPort<uint64_t, uint64_t>>*     host_data_slv;
    DMAEngine<AXIPort<uint32_t, uint64_t>>*     host_data_mst;
    DMAEngine<AXIPort<uint32_t, uint64_t>>*     ni_data_mst;
    DMAEngine<AXIPort<uint32_t, uint64_t>>*     no_data_mst;
    NIMaster*                                   ni_ctrl_mst;
    NOSlave*                                    no_ctrl_slv;
};

}