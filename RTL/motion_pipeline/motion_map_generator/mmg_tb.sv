/*------------------------------------------------------------------------------
 * File          : mmg_tb.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 17, 2025
 * Description   : UVM testbench for motion_map_generator
 *------------------------------------------------------------------------------*/
module mmg_tb;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Instantiate interface
  mmg_if vif();

  // Instantiate DUT
  motion_map_generator dut (
	.clk             (vif.clk),
	.rst             (vif.rst),
	.enable          (vif.enable),
	.pixel           (vif.pixel),
	.last_in_frame   (vif.last_in_frame),
	.wr_background   (vif.wr_background),
	.threshold       (vif.threshold),
	.motion_detected (vif.motion_detected)
  );

  // Clock generation: 100 MHz (~10 ns period)
  initial begin
	vif.clk = 0;
	forever #5 vif.clk = ~vif.clk;
  end

  // Reset sequence
  initial begin
	vif.rst = 1;
	#20;
	vif.rst = 0;
  end

  // UVM configuration and run
  initial begin
	uvm_config_db#(virtual mmg_if)::set(null, "*", "vif", vif);
	run_test("mmg_test");
  end

  covergroup cg_mmg @(posedge vif.clk);
	  option.per_instance = 1;
	  option.goal = 100;  // Optional: define a target coverage goal

	  // --------------------------------------------------------
	  // Basic control signal coverage
	  // --------------------------------------------------------
	  last_frame_cp: coverpoint vif.last_in_frame  { bins boundary   = {1}; bins midframe   = {0}; }
	  wr_bg_cp:      coverpoint vif.wr_background  { bins write_bg   = {1}; bins no_write   = {0}; }

	  // --------------------------------------------------------
	  // Threshold coverage (important for motion sensitivity)
	  // --------------------------------------------------------
	  /*threshold_cp: coverpoint vif.threshold {
		bins low_     = {[1:10]};         // Very sensitive
		bins medium_  = {[11:128]};       // Typical case
		bins high_    = {[129:255]};      // Very strict
		bins zero    = {0};              // Corner case
		bins max     = {255};            // Extreme case
	  }*/

	  // --------------------------------------------------------
	  // Pixel value coverage (coarse-grained buckets)
	  // --------------------------------------------------------
	  pixel_cp: coverpoint vif.pixel {
		bins black     = {32'h00000000};
		bins dark      = {[32'h00000001 : 32'h0FFFFFFF]};
		bins mid       = {[32'h10000000 : 32'h7FFFFFFF]};
		bins bright    = {[32'h80000000 : 32'hEFFFFFFF]};
		bins white     = {32'hFFFFFFFF};
	  }

	  // --------------------------------------------------------
	  // Motion detection output coverage
	  // --------------------------------------------------------
	  motion_cp: coverpoint vif.motion_detected { bins detected = {1}; bins idle = {0}; }

	  // --------------------------------------------------------
	  // CROSS COVERAGE for meaningful combinations
	  // --------------------------------------------------------

	  // 1. Cross between wr_background and motion_detected
	  wr_motion_x: cross wr_bg_cp, motion_cp;

	  // 2. Cross between threshold ranges & motion_detected
	 // threshold_motion_x: cross threshold_cp, motion_cp;

	  // 3. Cross between frame boundary and motion detection
	  frame_motion_x: cross last_frame_cp, motion_cp;

	  // 4. Cross between pixel brightness and motion detection
	  pixel_motion_x: cross pixel_cp, motion_cp;

	endgroup

  // Instantiate and sample coverage
  cg_mmg mmg_coverage;
  initial mmg_coverage = new();

endmodule : mmg_tb
