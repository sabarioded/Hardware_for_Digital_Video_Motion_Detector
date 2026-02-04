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

  covergroup cg_md @(posedge vif.clk);
	  option.per_instance = 1;
	  option.name = "motion_detector_cov";

	  // --------------------------------------------------
	  // 1. Control States
	  // --------------------------------------------------

	  enable_cp: coverpoint vif.enable {
		bins enabled    = {1};
		bins disabled   = {0};
	  }
	  
	  // --------------------------------------------------
	  // 2. Pixel Inputs (basic value ranges)
	  // --------------------------------------------------
	  curr_pixel_cp: coverpoint vif.curr_pixel {
		bins min_val  = {8'd0};
		bins low_val  = {[8'd1:8'd50]};
		bins mid_val  = {[8'd51:8'd200]};
		bins high_val = {[8'd201:8'd254]};
		bins max_val  = {8'd255};
	  }

	  prev_pixel_cp: coverpoint vif.prev_pixel {
		bins min_val  = {8'd0};
		bins low_val  = {[8'd1:8'd50]};
		bins mid_val  = {[8'd51:8'd200]};
		bins high_val = {[8'd201:8'd254]};
		bins max_val  = {8'd255};
	  }

	  pixel_value_cross: cross curr_pixel_cp, prev_pixel_cp;

	  // --------------------------------------------------
	  // 3. Pixel Difference Metrics (absolute diff)
	  // --------------------------------------------------
	  pixel_diff_cp: coverpoint (
		(vif.curr_pixel > vif.prev_pixel) ?
		  (vif.curr_pixel - vif.prev_pixel) :
		  (vif.prev_pixel - vif.curr_pixel)
	  ) {
		bins zero_diff     = {8'd0};
		bins very_small    = {[1:5]};
		bins small_         = {[6:20]};
		bins medium_        = {[21:50]};
		bins large_         = {[51:150]};
		bins very_large    = {[151:255]};
	  }

	  bg_diff_cp: coverpoint (
		(vif.curr_pixel > vif.background) ?
		  (vif.curr_pixel - vif.background) :
		  (vif.background - vif.curr_pixel)
	  ) {
		bins zero_diff     = {8'd0};
		bins very_small    = {[1:5]};
		bins small_         = {[6:20]};
		bins medium_        = {[21:50]};
		bins large_         = {[51:150]};
		bins very_large    = {[151:255]};
	  }

	  diff_cross: cross pixel_diff_cp, bg_diff_cp;

	  // --------------------------------------------------
	  // 4. Output Behavior
	  // --------------------------------------------------
	  motion_detected_cp: coverpoint vif.motion_detected {
		bins motion_yes = {1};
		bins motion_no  = {0};
	  }

	  // --------------------------------------------------
	  // 5. Functional Crosses
	  // --------------------------------------------------
	  diff_motion_cross: cross pixel_diff_cp, motion_detected_cp {
		bins correct_detect    = binsof(pixel_diff_cp.large_) && binsof(motion_detected_cp.motion_yes);
		bins correct_no_motion = binsof(pixel_diff_cp.zero_diff) && binsof(motion_detected_cp.motion_no);
		bins borderline_yes = binsof(pixel_diff_cp.medium_) && binsof(motion_detected_cp.motion_yes);
		bins borderline_no  = binsof(pixel_diff_cp.medium_) && binsof(motion_detected_cp.motion_no);

	  }

	  control_motion_cross: cross enable_cp, motion_detected_cp {
		bins disabled_should_be_no = binsof(enable_cp.disabled) && binsof(motion_detected_cp.motion_no);
	  }

	endgroup



  // Instantiate and rely on implicit sampling via @(posedge vif.clk)
  cg_md md_cov = new();

endmodule : motion_detector_tb
