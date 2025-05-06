/*------------------------------------------------------------------------------
 * File          : sigma_delta_tb.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 5, 2025
 * Description   :
 *------------------------------------------------------------------------------*/
module sigma_delta_tb;

import uvm_pkg::*;
`include "uvm_macros.svh"

sigma_delta_if vif();

// Instantiate the DUT
sigma_delta_update dut (
	.clk(vif.clk),
	.rst(vif.rst),
	.enable(vif.enable),
	.wr_background(vif.wr_background),
	.curr_pixel(vif.curr_pixel),
	.background(vif.background),
	.variance(vif.variance),
	.background_next(vif.background_next),
	.variance_next(vif.variance_next),
	.motion_detected(vif.motion_detected)
);

// Instantiate the assertions
sigma_delta_assertions assertions (
	.clk(vif.clk),
	.rst(vif.rst),
	.enable(vif.enable),
	.wr_background(vif.wr_background),
	.curr_pixel(vif.curr_pixel),
	.background(vif.background),
	.variance(vif.variance),
	.background_next(vif.background_next),
	.variance_next(vif.variance_next),
	.motion_detected(vif.motion_detected)
);

initial begin
	uvm_config_db#(virtual sigma_delta_if)::set(null, "*", "vif", vif);
	run_test("sigma_delta_test");
end

// 35 MHz clock -> ~14.285 ns period
initial begin
	vif.clk = 0;
	forever #14.285 vif.clk = ~vif.clk;
end

endmodule

