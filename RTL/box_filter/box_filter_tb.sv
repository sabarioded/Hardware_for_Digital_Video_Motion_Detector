/*------------------------------------------------------------------------------
 * File          : box_filter_tb.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module box_filter_tb;

import uvm_pkg::*;
`include "uvm_macros.svh"

box_filter_if vif();

// === Instantiate the DUT ===
box_filter dut (
	.clk             (vif.clk),
	.rst             (vif.rst),
	.enable          (vif.enable),
	.neighbors_number      (vif.neighbors_number),
	.motion_map        (vif.motion_map),
	.filtered_motion      (vif.filtered_motion)
);

// === Instantiate the Assertions ===
box_filter_assertions assertions (
	.clk             (vif.clk),
	.rst             (vif.rst),
	.enable          (vif.enable),
	.neighbors_number      (vif.neighbors_number),
	.motion_map        (vif.motion_map),
	.filtered_motion      (vif.filtered_motion)
);

// === UVM Configuration ===
initial begin
	uvm_config_db#(virtual box_filter_if)::set(null, "*", "vif", vif);
	run_test("box_filter_test");
end

// === Clock Generation: 35 MHz => ~14.285 ns period ===
initial begin
	vif.clk = 0;
	forever #14.285 vif.clk = ~vif.clk;
end

endmodule

