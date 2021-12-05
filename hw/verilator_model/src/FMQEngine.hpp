#pragma once

#include "Vpspin_verilator.h"
#include "verilated.h"
#include "SimModule.hpp"
#include "AXIMaster.hpp"
#include "pspin.hpp"
#include "spin.h"
#include "pspinsim.h"


namespace PsPIN
{
    class FMQEngine : public SimModule
    {


    public:

        FMQEngine(fmq_control_port_concrete_t& input_port) : input_port(input_port)
        {
            //clean port state
            memset(&(this->input_port), 0, sizeof(fmq_control_port_concrete_t));

            //set her ready
            this->input_port.her_ready_o = 1;
        
            //set feedback NOT valid
            this->input_port.feedback_valid_o = 0;

        }


        void posedge()
        {
            if (input_port.her_ready_o && input_port.her_valid_i) 
            {
                printf("Got task!!!\n");
            }
        }

        void negedge()
        {

        }    

        void print_stats()
        {

        }


    private:
        fmq_control_port_concrete_t& input_port;

    };

}