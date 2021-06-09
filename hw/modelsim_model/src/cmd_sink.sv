// Copyright (c) 2021 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module cmd_sink #(
    parameter int unsigned BUFF_SIZE = 4,
    parameter int unsigned LATENCY = 10,
    parameter type cmd_req_t = logic,
    parameter type cmd_resp_t = logic
) (
    input logic                        clk_i,
    input logic                        rst_ni,

    output logic                       cmd_ready_o,
    input  logic                       cmd_valid_i,
    input  cmd_req_t                   cmd_i,

    output logic                       cmd_resp_valid_o,
    output cmd_resp_t                  cmd_resp_o
);

    logic fifo_resp_full, fifo_resp_empty, fifo_resp_pop;
    cmd_resp_t new_resp;

    logic [$clog2(LATENCY)-1:0] timer_d, timer_q;

    assign new_resp.cmd_id = cmd_i.cmd_id;
    assign cmd_ready_o = ~fifo_resp_full;
    assign fifo_resp_pop = (~timer_q == '0);

    assign cmd_resp_valid_o = fifo_resp_pop;

    fifo_v3 #(
        .dtype     (cmd_resp_t),
        .DEPTH     (BUFF_SIZE)
    ) i_resp_fifo (
        .clk_i     (clk_i),
        .rst_ni    (rst_ni),
        .flush_i   (1'b0),
        .testmode_i(1'b0),
        .full_o    (fifo_resp_full),
        .empty_o   (fifo_resp_empty),
        .usage_o   (),
        .data_i    (new_resp),
        .push_i    (cmd_valid_i && cmd_ready_o),
        .data_o    (cmd_resp_o),
        .pop_i     (fifo_resp_pop)
    );

    always_comb begin 
        timer_d = timer_q;

        if (fifo_resp_empty) begin
            timer_d = '0;
        end
        else begin
            timer_d = timer_q + 1;
        end
    end

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
            timer_q <= '0;
        end else begin
            timer_q <= timer_d;
        end
    end

endmodule