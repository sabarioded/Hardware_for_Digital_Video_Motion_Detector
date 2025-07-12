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
	//option.goal = 90;

	// Control signals
	rst_cp:             coverpoint vif.rst             { bins active = {1}; bins inactive = {0}; }
	enable_cp:          coverpoint vif.enable          { bins on = {1}; bins off = {0}; }
	motion_pixel_cp:    coverpoint vif.motion_pixel    { bins motion = {1}; bins no_motion = {0}; }
	last_in_frame_cp:   coverpoint vif.last_in_frame   { bins frame_ended = {1}; bins frame_didnt_end = {0}; }

	// Input Label Values
	left_label_cp: coverpoint vif.left_label {
		bins zero = {0};
		bins low_range  = {[1 : max_label_val_p / 3]};
		bins mid_range  = {[max_label_val_p / 3 + 1 : max_label_val_p * 2 / 3]};
		bins high_range = {[max_label_val_p * 2 / 3 + 1 : max_label_val_p]};
	}
	top_label_cp: coverpoint vif.top_label {
		bins zero = {0};
		bins low_range  = {[1 : max_label_val_p / 3]};
		bins mid_range  = {[max_label_val_p / 3 + 1 : max_label_val_p * 2 / 3]};
		bins high_range = {[max_label_val_p * 2 / 3 + 1 : max_label_val_p]};
	}

	// Output Control Signals
	new_label_valid_cp: coverpoint vif.new_label_valid { bins alloc = {1}; bins no_alloc = {0}; }
	merge_labels_cp:    coverpoint vif.merge_labels    { bins do_merge = {1}; bins no_merge = {0}; }

	// Output Label Values (Conditional Bins using 'iff')
	new_label_value_cp: coverpoint vif.new_label_value iff (vif.new_label_valid) {
		bins non_zero = {[1 : max_label_val_p]};
		ignore_bins zero_value = {0};
	}
	merge_a_cp: coverpoint vif.merge_a iff (vif.merge_labels) {
		bins non_zero = {[1 : max_label_val_p]};
		ignore_bins zero_value = {0};
	}
	merge_b_cp: coverpoint vif.merge_b iff (vif.merge_labels) {
		bins non_zero = {[1 : max_label_val_p]};
		ignore_bins zero_value = {0};
	}
	current_label_cp: coverpoint vif.current_label iff (vif.enable && vif.motion_pixel) {
		bins non_zero = {[1 : max_label_val_p]};
		ignore_bins zero_label = {0};
	}

	// Cross-coverage (relying on implicit bins only, no explicit bin definitions here)
	neighbor_modes_cross: cross left_label_cp, top_label_cp;
	merge_conditions_cross: cross left_label_cp, top_label_cp, merge_labels_cp, merge_a_cp, merge_b_cp;
	new_label_assignment_cross: cross new_label_valid_cp, new_label_value_cp;
	next_label_increment_cross: cross motion_pixel_cp, new_label_valid_cp, last_in_frame_cp;
	next_label_reset_cross: cross rst_cp, last_in_frame_cp, enable_cp;
	control_signal_active_cross: cross enable_cp, motion_pixel_cp;

endgroup

// Instantiate and sample coverage
cg_labler labler_coverage = new(255);

endmodule
