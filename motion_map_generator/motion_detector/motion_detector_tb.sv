/*------------------------------------------------------------------------------
 * File          : motion_detector_tb.sv (with functional coverage)
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   : UVM testbench for motion_detector with added covergroup
 *------------------------------------------------------------------------------*/
module motion_detector_tb;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Instantiate interface
  motion_detector_if vif();

  // Instantiate DUT
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

  //------------------------------------------------------------------------------
  // Clock Generation: 35 MHz => ~14.285 ns period
  //------------------------------------------------------------------------------
  initial begin
	vif.clk = 0;
	forever #14.285 vif.clk = ~vif.clk;
  end

  // Reset sequence
  initial begin
	vif.rst = 1;
	#10;
	vif.rst = 0;
  end
  //------------------------------------------------------------------------------
  // UVM Configuration and run
  //------------------------------------------------------------------------------
  initial begin
	uvm_config_db#(virtual motion_detector_if)::set(null, "*", "vif", vif);
	run_test("motion_detector_test");
  end

  //------------------------------------------------------------------------------
  // Functional coverage: covergroup sampling on clock edge
  //------------------------------------------------------------------------------
  covergroup cg_md @(posedge vif.clk);
	option.per_instance = 1;

	// Reset and enable
	rst_cp:      coverpoint vif.rst        { bins active = {1}; bins inactive = {0}; }
	enable_cp:   coverpoint vif.enable     { bins on     = {1}; bins off      = {0}; }

	// Pixel inputs
	curr_cp:     coverpoint vif.curr_pixel { bins min={8'd0}; bins max={8'd255}; bins mid={[8'd1:8'd254]}; }
	prev_cp:     coverpoint vif.prev_pixel { bins min={8'd0}; bins max={8'd255}; bins mid={[8'd1:8'd254]}; }

	// Internal difference signals
	pixel_diff_cp: coverpoint ((vif.curr_pixel>vif.prev_pixel)
							  ? vif.curr_pixel-vif.prev_pixel
							  : vif.prev_pixel-vif.curr_pixel) {
		bins zero = {8'd0};
		bins low = {[8'd1:8'd20]};
		bins mid = {[8'd21:8'd100]};
		bins high = {[8'd101:8'd200]};
		bins very_high = {[8'd201:8'd255]};
	}
	bg_diff_cp:    coverpoint ((vif.curr_pixel>vif.background)
							  ? vif.curr_pixel-vif.background
							  : vif.background-vif.curr_pixel) {
	  bins zero = {8'd0};
	  bins low = {[8'd1:8'd20]};
	  bins mid = {[8'd21:8'd100]};
	  bins high = {[8'd101:8'd200]};
	  bins very_high = {[8'd201:8'd255]};
	}

	// Output coverage
	motion_cp:   coverpoint vif.motion_detected { bins no={0}; bins yes={1}; }

  endgroup

  // Instantiate and rely on implicit sampling via @(posedge vif.clk)
  cg_md md_cov = new();

endmodule : motion_detector_tb
