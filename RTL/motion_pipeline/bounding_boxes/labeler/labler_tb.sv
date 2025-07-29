/*------------------------------------------------------------------------------
 * File          : labler_tb.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 24, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module labler_tb;
import uvm_pkg::*;
`include "uvm_macros.svh"

labler_if vif();

labeler dut(
  .clk             (vif.clk),
  .rst             (vif.rst),
  .enable          (vif.enable),
  .last_in_frame   (vif.last_in_frame),
  .motion_pixel    (vif.motion_pixel),
  .left_label      (vif.left_label),
  .top_label       (vif.top_label),
  .new_label_valid (vif.new_label_valid),
  .new_label_value (vif.new_label_value),
  .merge_labels    (vif.merge_labels),
  .merge_a         (vif.merge_a),
  .merge_b         (vif.merge_b),
  .current_label   (vif.current_label)
);

initial begin
  vif.clk = 0;
  forever #5 vif.clk = ~vif.clk;
end

initial begin
  vif.rst = 1;
  vif.enable = 0;
  #10;
  vif.rst = 0;
end

// UVM configuration and run
initial begin
  uvm_config_db#(virtual labler_if)::set(null, "*", "vif", vif);
  run_test("labler_test");
end

covergroup cg_labler (int max_label_val_p) @(posedge vif.clk);
	option.per_instance = 1;
	option.name = "labeler_coverage";

	// ==========================================================================
	// 1. Control Signals
	// ==========================================================================
	enable_cp: coverpoint vif.enable { bins on = {1}; bins off = {0}; }
	motion_pixel_cp: coverpoint vif.motion_pixel { bins motion = {1}; bins no_motion = {0}; }
	last_in_frame_cp: coverpoint vif.last_in_frame { bins end_frame = {1}; bins mid = {0}; }

	// ==========================================================================
	// 2. Input Labels
	// ==========================================================================
	left_label_cp: coverpoint vif.left_label {
	  bins zero       = {0};
	  bins low_range  = {[1 : max_label_val_p/3]};
	  bins mid_range  = {[max_label_val_p/3+1 : (2*max_label_val_p)/3]};
	  bins high_range = {[((2*max_label_val_p)/3)+1 : max_label_val_p]};
	}

	top_label_cp: coverpoint vif.top_label {
	  bins zero       = {0};
	  bins low_range  = {[1 : max_label_val_p/3]};
	  bins mid_range  = {[max_label_val_p/3+1 : (2*max_label_val_p)/3]};
	  bins high_range = {[((2*max_label_val_p)/3)+1 : max_label_val_p]};
	}

	// Explicit bin for equality detection
	neighbor_equal_cp: coverpoint (vif.left_label == vif.top_label) iff (vif.left_label!=0 && vif.top_label!=0) {
	  bins equal = {1};
	  bins not_equal = {0};
	}

	// ==========================================================================
	// 3. Output Signals
	// ==========================================================================
	new_label_valid_cp: coverpoint vif.new_label_valid { bins allocated = {1}; bins not_allocated = {0}; }
	merge_labels_cp: coverpoint vif.merge_labels { bins merged = {1}; bins not_merged = {0}; }

	new_label_value_cp: coverpoint vif.new_label_value iff (vif.new_label_valid) {
	  bins valid_values = {[1 : max_label_val_p]};
	  ignore_bins zero = {0};
	}

	merge_a_cp: coverpoint vif.merge_a iff (vif.merge_labels) {
	  bins valid_a = {[1 : max_label_val_p]};
	  ignore_bins zero = {0};
	}

	merge_b_cp: coverpoint vif.merge_b iff (vif.merge_labels) {
	  bins valid_b = {[1 : max_label_val_p]};
	  ignore_bins zero = {0};
	}

	current_label_cp: coverpoint vif.current_label iff (vif.enable && vif.motion_pixel) {
	  bins assigned = {[1 : max_label_val_p]};
	  ignore_bins zero = {0};
	}

	// ==========================================================================
	// 4. Behavioral Crosses
	// ==========================================================================

	// (A) Cross: Merge and motion
	merge_motion_cross: cross motion_pixel_cp, merge_labels_cp {
	  bins merged_motion    = binsof(motion_pixel_cp.motion) && binsof(merge_labels_cp.merged);
	  bins no_merge_motion  = binsof(motion_pixel_cp.motion) && binsof(merge_labels_cp.not_merged);
	  bins merged_idle      = binsof(motion_pixel_cp.no_motion) && binsof(merge_labels_cp.merged); // should be rare/bug
	}

	// (B) Cross: Label allocation
	new_label_cross: cross motion_pixel_cp, new_label_valid_cp {
	  bins allocated_for_motion = binsof(motion_pixel_cp.motion) && binsof(new_label_valid_cp.allocated);
	  bins no_alloc_no_motion   = binsof(motion_pixel_cp.no_motion) && binsof(new_label_valid_cp.not_allocated);
	}

	// (C) Cross: Frame boundary + merge
	frame_boundary_merge_cross: cross last_in_frame_cp, merge_labels_cp {
	  bins merge_at_boundary = binsof(last_in_frame_cp.end_frame) && binsof(merge_labels_cp.merged);
	  bins merge_in_midframe = binsof(last_in_frame_cp.mid) && binsof(merge_labels_cp.merged);
	}

	// (D) Cross: Current label vs allocation
	label_assignment_cross: cross current_label_cp, new_label_valid_cp {
	  bins assigned_with_new  = binsof(current_label_cp.assigned) && binsof(new_label_valid_cp.allocated);
	}

  endgroup

// Instantiate and sample coverage
  cg_labler labler_coverage = new(255);

endmodule
