/*------------------------------------------------------------------------------
 * File          : sigma_delta_tb.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 5, 2025
 * Description   : UVM testbench for sigma_delta
 *------------------------------------------------------------------------------*/
module sigma_delta_tb;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  sigma_delta_if vif();

  // Instantiate DUT
  sigma_delta dut (
    .clk            (vif.clk),
    .rst            (vif.rst),
    .enable         (vif.enable),
    .wr_background  (vif.wr_background),
    .curr_pixel     (vif.curr_pixel),
    .background     (vif.background),
    .variance       (vif.variance),
    .background_next(vif.background_next),
    .variance_next  (vif.variance_next)
  );

  covergroup cg_sigma_delta @(posedge vif.clk);
	  option.per_instance = 1;
	  option.name = "sigma_delta_cov";

	  // --------------------------------------------------------
	  // 1. CONTROL SIGNALS
	  // --------------------------------------------------------

	  enable_cp: coverpoint vif.enable {
		bins active = {1};
		bins idle   = {0};
	  }

	  wr_bg_cp: coverpoint vif.wr_background {
		bins write_req = {1};
		bins no_write  = {0};
	  }

	  ctrl_cross: cross enable_cp, wr_bg_cp {
		bins write_when_enabled = binsof(enable_cp.active) && binsof(wr_bg_cp.write_req);
		bins idle_no_write      = binsof(enable_cp.idle)   && binsof(wr_bg_cp.no_write);
	  }

	  // --------------------------------------------------------
	  // 2. PIXEL INPUTS
	  // --------------------------------------------------------
	  curr_pixel_cp: coverpoint vif.curr_pixel {
		bins zero    = {8'd0};
		bins low     = {[1:63]};
		bins mid     = {[64:191]};
		bins high    = {[192:254]};
		bins max     = {8'd255};
	  }

	  background_cp: coverpoint vif.background {
		bins zero    = {8'd0};
		bins low     = {[1:63]};
		bins mid     = {[64:191]};
		bins high    = {[192:254]};
		bins max     = {8'd255};
	  }

	  variance_cp: coverpoint vif.variance {
		bins min     = {8'd2};              // startup default
		bins near_low = {[3:4]};            // just above lower bound
		bins normal  = {[5:250]};           // normal operating band
		bins high = {[251:255]};       // close to saturation
	  }

	  // --------------------------------------------------------
	  // 3. INTERNAL MOTION DELTA (absolute difference)
	  // --------------------------------------------------------
	  diff_cp: coverpoint ((vif.curr_pixel > vif.background)
						  ?  vif.curr_pixel - vif.background
						   : vif.background - vif.curr_pixel) {
		bins exact_zero   = {0};             // identical pixel vs background
		bins very_small   = {[1:4]};         // tiny diff
		bins small_        = {[5:20]};        // minor changes
		bins medium_       = {[21:100]};      // normal motion
		bins large_        = {[101:200]};     // significant change
		bins very_large   = {[201:255]};     // extreme change
	  }

	  // --------------------------------------------------------
	  // 4. OUTPUTS - NEXT BACKGROUND AND VARIANCE
	  // --------------------------------------------------------
	  bg_next_cp: coverpoint vif.background_next {
		bins zero    = {8'd0};
		bins low     = {[1:63]};
		bins mid     = {[64:191]};
		bins high    = {[192:254]};
		bins max     = {8'd255};
	  }

	  variance_next_cp: coverpoint vif.variance_next {
		bins min         = {8'd2};          // initial value
		bins near_low    = {[3:4]};
		bins normal      = {[5:150]};
		bins near_high   = {[151:255]};
	  }

	  // --------------------------------------------------------
	  // 5. IMPORTANT CROSSES
	  // --------------------------------------------------------

	  // Cross pixel difference vs variance  see triggering conditions
	  diff_vs_variance_cross: cross diff_cp, variance_cp {
		bins diff_gt_var = binsof(diff_cp.large_) && binsof(variance_cp.normal);
		bins diff_lt_var = binsof(diff_cp.small_) && binsof(variance_cp.high);
		bins diff_eq_var = binsof(diff_cp.medium_) && binsof(variance_cp.normal);
	  }

	  // Cross curr_pixel vs background  test all relative relationships
	  pixel_bg_relation_cross: cross curr_pixel_cp, background_cp {
		bins equal_pixels = binsof(curr_pixel_cp.zero) && binsof(background_cp.zero);
		bins lower_bg     = binsof(curr_pixel_cp.low)  && binsof(background_cp.high);
		bins higher_bg    = binsof(curr_pixel_cp.high) && binsof(background_cp.low);
	  }

	  // Cross variance_next vs diff to ensure coverage of increment/decrement
	  diff_vs_varnext_cross: cross diff_cp, variance_next_cp {
		bins increment_event = binsof(diff_cp.large_) && binsof(variance_next_cp.near_high);
		bins decrement_event = binsof(diff_cp.small_) && binsof(variance_next_cp.near_low);
		bins steady_event    = binsof(diff_cp.exact_zero) && binsof(variance_next_cp.normal);
	  }

	  // Control + outputs cross (ensure writes only when enabled)
	  control_output_cross: cross enable_cp, wr_bg_cp, bg_next_cp {
		bins valid_write = binsof(enable_cp.active) && binsof(wr_bg_cp.write_req);
		bins ignored_write = binsof(enable_cp.idle) && binsof(wr_bg_cp.write_req);
	  }

	endgroup

  // Instantiate and sample the covergroup
  cg_sigma_delta coverage_inst;
  initial begin
    coverage_inst = new();
  end

  // UVM run
  initial begin
    uvm_config_db#(virtual sigma_delta_if)::set(null, "*", "vif", vif);
    run_test("sigma_delta_test");
  end

  // 35 MHz clock generation -> ~14.285 ns period
  initial begin
    vif.clk = 0;
    forever #14.285 vif.clk = ~vif.clk;
  end

endmodule : sigma_delta_tb
