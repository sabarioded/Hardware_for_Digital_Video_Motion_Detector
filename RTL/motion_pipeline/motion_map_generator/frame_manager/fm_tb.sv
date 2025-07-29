/*------------------------------------------------------------------------------
 * File          : fm_tb.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 15, 2025
 * Description   : UVM testbench for frame_manager with functional coverage
 *------------------------------------------------------------------------------*/
module fm_tb;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Instantiate interface
  fm_if vif();

  // Instantiate DUT
  frame_manager dut (
    .clk            (vif.clk),
    .rst            (vif.rst),
    .enable         (vif.enable),
    .pixel          (vif.pixel),
    .last_in_frame  (vif.last_in_frame),
    .curr_pixel     (vif.curr_pixel),
    .prev_pixel     (vif.prev_pixel),
    .wr_background  (vif.wr_background),
    .background_next(vif.background_next),
    .variance_next  (vif.variance_next)
  );

  // Clock generation: 100MHz (10ns)
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

  covergroup cg_fm @(posedge vif.clk);
	  option.per_instance = 1;
	  option.name = "frame_manager_cov";

	  // ----------------------------------------
	  // Control signal coverage
	  // ----------------------------------------
	  rst_cp: coverpoint vif.rst {
		bins active   = {1};
		bins inactive = {0};
	  }

	  enable_cp: coverpoint vif.enable {
		bins on  = {1};
		bins off = {0};
	  }

	  last_frame_cp: coverpoint vif.last_in_frame {
		bins asserted = {1};
		bins idle     = {0};
	  }

	  wr_bg_cp: coverpoint vif.wr_background {
		bins write    = {1};
		bins no_write = {0};
	  }

	  // Cross coverage for control states (frame boundary + enable)
	  control_cross: cross enable_cp, last_frame_cp, wr_bg_cp {

		  // Ignore cases where enable=off and wr_bg_cp=write (shouldn?t affect coverage)
		  ignore_bins ignored_when_disabled =
			  binsof(enable_cp.off) &&
			  binsof(wr_bg_cp.write);

		}


	  // ----------------------------------------
	  // Pixel input (32-bit RGBX)
	  // ----------------------------------------
	  pixel_cp: coverpoint vif.pixel {
		bins low     = {[32'h00000000:32'h3FFFFFFF]};       // low intensity
		bins mid_lo  = {[32'h40000000:32'h7FFFFFFF]};       // mid lower
		bins mid_hi  = {[32'h80000000:32'hBFFFFFFF]};       // mid upper
		bins high    = {[32'hC0000000:32'hFFFFFFFF]};       // bright colors
	  }

	  // ----------------------------------------
	  // Grayscale outputs
	  // ----------------------------------------
	  curr_cp: coverpoint vif.curr_pixel {
		bins min     = {8'd0};
		bins low     = {[1:63]};
		bins mid     = {[64:191]};
		bins high    = {[192:255]};
	  }

	  prev_cp: coverpoint vif.prev_pixel {
		bins min     = {8'd0};
		bins low     = {[1:63]};
		bins mid     = {[64:191]};
		bins high    = {[192:255]};
	  }

	  // Cross coverage for pixel progression
	  pixel_progress_cross: cross curr_cp, prev_cp {
		bins unchanged = binsof(curr_cp.min) && binsof(prev_cp.min);
		bins low_to_high = binsof(curr_cp.high) && binsof(prev_cp.low);
		bins high_to_low = binsof(curr_cp.low) && binsof(prev_cp.high);
		bins stable_mid  = binsof(curr_cp.mid) && binsof(prev_cp.mid);
	  }

	  // ----------------------------------------
	  // Sigma-delta outputs: background_next / variance_next
	  // ----------------------------------------
	  bg_next_cp: coverpoint vif.background_next {
		bins min     = {0};
		bins low     = {[1:63]};
		bins mid     = {[64:191]};
		bins high    = {[192:255]};
	  }

	  var_next_cp: coverpoint vif.variance_next {
		bins init_reset = {2};               // default after reset
		bins low        = {[3:20]};           // small variance
		bins mid        = {[21:255]};        // normal operating range
	  }

	  // Cross coverage for sigma-delta evolution
	  bg_var_cross: cross bg_next_cp, var_next_cp {
		bins stable_low_bg    = binsof(bg_next_cp.low) && binsof(var_next_cp.low);
		bins stable_mid_bg    = binsof(bg_next_cp.mid) && binsof(var_next_cp.mid);
		bins background_adapt = binsof(bg_next_cp.high) && binsof(var_next_cp.mid);
	  }

	  // ----------------------------------------
	  // Frame boundary behavior
	  // ----------------------------------------
	  frame_boundary_transition: coverpoint vif.last_in_frame iff (vif.enable) {
		bins boundary_seen = (0 => 1);   // transition to frame end
		bins restart_seen  = (1 => 0);   // start of new frame
	  }

	  // Combine boundary with pixel behavior
	  boundary_pixel_cross: cross last_frame_cp, curr_cp, prev_cp {
		  
		  ignore_bins idle_min_cases =
			  binsof(last_frame_cp.idle) &&
			  binsof(curr_cp.min) &&
			  ( binsof(prev_cp.high) || binsof(prev_cp.mid) || binsof(prev_cp.low) );

		  ignore_bins asserted_high_lowmin =
			  binsof(last_frame_cp.asserted) &&
			  binsof(curr_cp.high) &&
			  ( binsof(prev_cp.low) || binsof(prev_cp.min) );

		  ignore_bins asserted_low_all =
			  binsof(last_frame_cp.asserted) &&
			  binsof(curr_cp.low) &&
			  ( binsof(prev_cp.mid) || binsof(prev_cp.low) || binsof(prev_cp.min) );

		  ignore_bins asserted_min_all =
			  binsof(last_frame_cp.asserted) &&
			  binsof(curr_cp.min) &&
			  ( binsof(prev_cp.high) || binsof(prev_cp.mid) || binsof(prev_cp.low) );

		}



	  // ----------------------------------------
	  // Complex cross: enable + last_frame + bg update
	  // ----------------------------------------
	  frame_ctrl_cross: cross enable_cp, last_frame_cp, wr_bg_cp, bg_next_cp {

		  // Ignore all ?off + write? bins
		  ignore_bins disabled_writes =
			  binsof(enable_cp.off) &&
			  binsof(wr_bg_cp.write);

		  // Ignore bins where bg_next is min when disabled
		  ignore_bins disabled_min_bg =
			  binsof(enable_cp.off) &&
			  binsof(bg_next_cp.min);
		}

	  

	endgroup


  // Instantiate and sample coverage
  cg_fm coverage_inst;
  initial begin
    coverage_inst = new();
  end

  // UVM run
  initial begin
    uvm_config_db#(virtual fm_if)::set(null, "*", "vif", vif);
    run_test("fm_test");
  end

endmodule : fm_tb
