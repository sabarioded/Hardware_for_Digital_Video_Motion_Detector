/*------------------------------------------------------------------------------
 * File          : motion_detector_tb.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module motion_detector_tb;

import uvm_pkg::*;
`include "uvm_macros.svh"

motion_detector_if vif();

// === Instantiate the DUT ===
motion_detector dut (
	.clk             (vif.clk),
	.rst             (vif.rst),
	.enable          (vif.enable),
	.background      (vif.background),
	.variance        (vif.variance),
	.curr_pixel      (vif.curr_pixel),
	.prev_pixel      (vif.prev_pixel),
	.threshold       (vif.threshold),
	.motion_detected (vif.motion_detected)
);

// === UVM Configuration ===
initial begin
	uvm_config_db#(virtual motion_detector_if)::set(null, "*", "vif", vif);
	run_test("motion_detector_test");
end

// === Clock Generation: 35 MHz => ~14.285 ns period ===
initial begin
	vif.clk = 0;
	forever #14.285 vif.clk = ~vif.clk;
end

endmodule

