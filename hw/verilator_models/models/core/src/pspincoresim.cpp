
#include "pspincoresim.hpp"

using namespace PsPIN;

#include "AXIPort.hpp"
#include "pspin.hpp"

PsPINCoreSim::PsPINCoreSim(std::string vcd_file_path) 
{
    Verilated::commandArgs(0, (char**) NULL);
    Vpspin_verilator *tb = new Vpspin_verilator();
    sim = new SimControl<Vpspin_verilator>(tb, vcd_file_path.c_str());

    // Define ports
    AXI_MASTER_PORT_ASSIGN(tb, ni_slave, &ni_data_mst_port);
    AXI_MASTER_PORT_ASSIGN(tb, no_slave, &no_data_mst_port);
    NI_CTRL_PORT_ASSIGN(tb, her, &ni_ctrl_mst_port)    
    NO_CMD_PORT_ASSIGN(tb, nic_cmd, &no_ctrl_slv_port);
    AXI_SLAVE_PORT_ASSIGN(tb, host_master, &host_slv_port);
    AXI_MASTER_PORT_ASSIGN(tb, host_slave, &host_mst_port);

    host_data_slv = new DMATarget<AXIPort<uint64_t, uint64_t>>(host_slv_port, 0, 0);
    host_data_mst = new DMAEngine<AXIPort<uint32_t, uint64_t>>(host_mst_port);
    
    ni_data_mst = new DMAEngine<AXIPort<uint32_t, uint64_t>>(ni_data_mst_port);
    no_data_mst = new DMAEngine<AXIPort<uint32_t, uint64_t>>(no_data_mst_port);

    ni_ctrl_mst = new NIMaster(ni_ctrl_mst_port);    
    no_ctrl_slv = new NOSlave(no_ctrl_slv_port);

    sim->add_module(*host_data_slv);
    sim->add_module(*host_data_mst);
    sim->add_module(*ni_data_mst);
    sim->add_module(*no_data_mst);
    sim->add_module(*ni_ctrl_mst);
    sim->add_module(*no_ctrl_slv);

    // Send reset signal
    sim->reset();
}

int PsPINCoreSim::run() 
{
    // Main loop
    sim->run_all();
    return SPIN_SUCCESS;
}

int PsPINCoreSim::step(uint8_t* done_flag)
{
    // Single step of the main loop
    *done_flag = 0;
    sim->run_single();
    if (sim->done()) *done_flag = 1;

    return SPIN_SUCCESS;
}

int PsPINCoreSim::shutdown()
{
    ni_ctrl_mst->shutdown();
    return SPIN_SUCCESS;
}

void PsPINCoreSim::printStats()
{
    printf("\n###### Statistics ######\n");
    for (auto it = sim->get_modules().begin(); it != sim->get_modules().end(); ++it){
        it->get().print_stats();
        printf("----------------------------------\n");
    }
}

int PsPINCoreSim::nicMemWrite(uint32_t addr, uint8_t *data, size_t size, WriteCompletedCallback cb)
{
    ni_data_mst->write(addr, data, size, cb);
    return SPIN_SUCCESS;
}

int PsPINCoreSim::nicMemRead(uint32_t addr, uint8_t *data, size_t size, ReadCompletedCallback cb)
{
    no_data_mst->read(addr, data, size, cb);
    return SPIN_SUCCESS;
}

int PsPINCoreSim::hostMemWrite(uint32_t addr, uint8_t *data, size_t size, WriteCompletedCallback cb)
{
    host_data_mst->write(addr, data, size, cb);
    return SPIN_SUCCESS;
}

int PsPINCoreSim::hostMemRead(uint32_t addr, uint8_t *data, size_t size, ReadCompletedCallback cb)
{
    host_data_mst->read(addr, data, size, cb);
    return SPIN_SUCCESS;
}

int PsPINCoreSim::sendHER(her_descr_t *her, HERCompletetionCallback cb)
{
    ni_ctrl_mst->send_her(her, cb);
    return SPIN_SUCCESS;
}

int PsPINCoreSim::setNICCommandCallback(NICCommandCallback cb) { 
    no_ctrl_slv->set_nic_command_cb(cb);
    return SPIN_SUCCESS;
}

int PsPINCoreSim::setHostWriteCallback(HostWriteCallback cb)
{
    host_data_slv->set_slv_write_cb(cb);
    return SPIN_SUCCESS;
}

int PsPINCoreSim::setHostReadCallback(HostReadCallback cb)
{
    host_data_slv->set_slv_read_cb(cb);
    return SPIN_SUCCESS;
}

bool PsPINCoreSim::setNICCommandStatus(bool blocked)
{
    bool status = no_ctrl_slv->is_blocked();
    if (blocked) no_ctrl_slv->block();
    else no_ctrl_slv->unblock();

    return status;
}

bool PsPINCoreSim::setHostWriteStatus(bool blocked)
{
    bool status = host_data_slv->is_write_blocked();
    if (blocked) host_data_slv->block_writes();
    else host_data_slv->unblock_writes();
    
    return status;
}

bool PsPINCoreSim::setHostReadStatus(bool blocked)
{
    bool status = host_data_slv->is_read_blocked();
    if (blocked) host_data_slv->block_reads();
    else host_data_slv->unblock_reads();
    
    return status;
}