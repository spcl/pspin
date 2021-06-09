// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module cluster_cmd #(
    parameter int unsigned NUM_CORES = 8,
    parameter int unsigned CLUSTER_ID_WIDTH = 16,
    parameter type cmd_req_t = logic,
    parameter type cmd_resp_t = logic
) (
    input  logic                        clk_i,
    input  logic                        rst_ni,

    input  logic [CLUSTER_ID_WIDTH-1:0] cluster_id_i,

    // from hpu drivers (commands)
    output logic [NUM_CORES-1:0]        cmd_ready_o,
    input  logic [NUM_CORES-1:0]        cmd_valid_i,
    input  cmd_req_t [NUM_CORES-1:0]    cmd_i,

    // to hpu drivers
    output logic                        cmd_resp_valid_o,
    output cmd_resp_t                   cmd_resp_o,

    // to uncluster 
    input  logic                        uncluster_cmd_ready_i,
    output logic                        uncluster_cmd_valid_o,
    output cmd_req_t                    uncluster_cmd_o,

    // from uncluster
    input  logic                        uncluster_cmd_resp_valid_i,
    input  cmd_resp_t                   uncluster_cmd_resp_i,

    // to cluster DMA engine
    input  logic                        dma_cmd_ready_i,
    output logic                        dma_cmd_valid_o,
    output cmd_req_t                    dma_cmd_o,

    // from DMA engine
    input  logic                        dma_cmd_resp_valid_i,
    input  cmd_resp_t                   dma_cmd_resp_i
);
    logic [NUM_CORES-1:0] intf_selector;
    logic uncluster_cmd_resp_valid;

    assign uncluster_cmd_resp_valid = (uncluster_cmd_resp_valid_i && dma_cmd_resp_i.cmd_id.cluster_id == cluster_id_i);

    for (genvar i = 0; i < NUM_CORES; i++) begin : gen_cmds_selector
        assign intf_selector[i] = (cmd_i[i].to_uncluster) ? 1'b1 : 1'b0;
    end
    
    cmd_xbar #(
        .CUT_SLV_PORTS               (1'b0),
        .NUM_SLV_PORTS               (NUM_CORES),
        .NUM_MST_PORTS               (2),
        .INTF_RESP_BUFF_SIZE         (2),
        .cmd_req_t                   (cmd_req_t),
        .cmd_resp_t                  (cmd_resp_t)
    ) i_cmd_xbar (
        .rst_ni                      (rst_ni),
        .clk_i                       (clk_i),

        //commands from cluster
        .cmd_ready_o                 (cmd_ready_o),
        .cmd_valid_i                 (cmd_valid_i),
        .cmd_i                       (cmd_i),
        .cmd_intf_selector_i         (intf_selector),

        //command responses to clusters
        .cmd_resp_valid_o            (cmd_resp_valid_o),
        .cmd_resp_o                  (cmd_resp_o),

        //command interfaces requests
        .intf_ready_i                ({uncluster_cmd_ready_i,  dma_cmd_ready_i}),
        .intf_valid_o                ({uncluster_cmd_valid_o,  dma_cmd_valid_o}),
        .intf_cmd_o                  ({uncluster_cmd_o,        dma_cmd_o      }),

        //command interfaces responses
        .intf_cmd_resp_valid_i       ({uncluster_cmd_resp_valid,   dma_cmd_resp_valid_i}),
        .intf_cmd_resp_i             ({uncluster_cmd_resp_i,       dma_cmd_resp_i      })
    );

endmodule
