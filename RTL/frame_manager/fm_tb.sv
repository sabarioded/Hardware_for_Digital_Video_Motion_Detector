/*------------------------------------------------------------------------------
 * File          : fm_tb.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 15, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module fm_tb;

import uvm_pkg::*;
`include "uvm_macros.svh"

  // instantiate interface
  fm_if vif();

  // instantiate DUT
  frame_manager dut (
	.clk            (vif.clk),
	.rst            (vif.rst),
	.enable			(vif.enable),
	.pixel			(vif.pixel),
	.last_in_frame	(vif.last_in_frame),
	.curr_pixel		(vif.curr_pixel),
	.prev_pixel		(vif.prev_pixel),
	.wr_background (vif.wr_background),
	.background_next(vif.background_next),
	.variance_next(vif.variance_next)
  );

  // clock generation
  initial begin
	vif.clk = 0;
	forever #5 vif.clk = ~vif.clk;
  end

  // reset sequence
  initial begin
	vif.rst = 1;
	#20;
	vif.rst = 0;
  end

  // UVM configuration and run
  initial begin
	// pass interface to driver and monitor
	uvm_config_db#(virtual fm_if)::set(null, "*", "vif", vif);

	run_test("fm_test");
  end

endmodule: fm_tb