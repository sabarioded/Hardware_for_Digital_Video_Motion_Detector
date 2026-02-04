/*------------------------------------------------------------------------------
 * File        : lm_tb.sv
 * Project     : Project_RTL
 * Author      : eposmk
 * Creation date : May 26, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module lm_tb;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  lm_if vif();

  label_merger dut(
	.clk            (vif.clk),
	.rst            (vif.rst),
	.enable         (vif.enable),
	.last_in_frame  (vif.last_in_frame),
	.merge_valid    (vif.merge_valid),
	.merge_a        (vif.merge_a),
	.merge_b        (vif.merge_b),
	.resolve_valid  (vif.resolve_valid),
	.resolve_label  (vif.resolve_label),
	.resolved_label (vif.resolved_label)
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

  initial begin
	uvm_config_db#(virtual lm_if)::set(null, "*", "vif", vif);
	run_test("lm_test");
  end

  covergroup cg_lm @(posedge vif.clk);
	option.per_instance = 1;
	option.name = "label_merger_cov";

	// --------------------------------------------------------------------
	// 1) Control Signals
	// --------------------------------------------------------------------
	enable_cp: coverpoint vif.enable {
	  bins enabled = {1};
	  bins disabled = {0};
	}

	merge_valid_cp: coverpoint vif.merge_valid {
	  bins merge_request = {1};
	  bins no_merge_request = {0};
	}

	resolve_valid_cp: coverpoint vif.resolve_valid {
	  bins resolve_request = {1};
	  bins no_resolve_request = {0};
	}

	last_frame_cp: coverpoint vif.last_in_frame {
	  bins end_frame = {1};
	  bins mid_frame = {0};
	}

	// --------------------------------------------------------------------
	// 2) Merge Inputs and Relation
	// --------------------------------------------------------------------
	merge_a_val_cp: coverpoint vif.merge_a iff (vif.merge_valid) {
	  bins zero_label = {0};
	  bins valid_label = {[1:254]};
	  bins max_label = {255};
	}

	merge_b_val_cp: coverpoint vif.merge_b iff (vif.merge_valid) {
	  bins zero_label = {0};
	  bins valid_label = {[1:254]};
	  bins max_label = {255};
	}

	merge_relation_cp: coverpoint (vif.merge_a == vif.merge_b) iff (vif.merge_valid) {
	  bins self_merge = {1};
	  bins different_merge = {0};
	}
	
	// --------------------------------------------------------------------
	// 3) Resolve Inputs, Outputs, and Relationship
	// --------------------------------------------------------------------
	resolve_label_cp: coverpoint vif.resolve_label iff (vif.resolve_valid) {
	  bins zero_label = {0};
	  bins valid_label = {[1:254]};
	  bins max_label = {255};
	}

	resolved_label_cp: coverpoint vif.resolved_label iff (vif.resolve_valid) {
	  bins zero_label = {0};
	  bins valid_label = {[1:254]};
	  bins max_label = {255};
	}

	resolve_eq_cp: coverpoint (vif.resolve_label == vif.resolved_label) iff (vif.resolve_valid) {
	  bins resolves_to_self  = {1};
	  bins resolves_to_other = {0};
	}

	resolve_relation_cross: cross resolve_eq_cp, resolved_label_cp {
	  bins self_valid     = binsof(resolve_eq_cp.resolves_to_self)  && binsof(resolved_label_cp.valid_label);
	  bins other_valid    = binsof(resolve_eq_cp.resolves_to_other) && binsof(resolved_label_cp.valid_label);
	  bins resolved_zero  = binsof(resolved_label_cp.zero_label);
	}

	// --------------------------------------------------------------------
	// 4) Edge Case Bins
	// --------------------------------------------------------------------
	merge_at_frame_end_cp: coverpoint vif.last_in_frame iff (vif.merge_valid) {
	  bins merge_at_boundary = {1};
	}

	resolve_at_frame_end_cp: coverpoint vif.last_in_frame iff (vif.resolve_valid) {
	  bins resolve_at_boundary = {1};
	}

	// --------------------------------------------------------------------
	// 5) Functional Crosses
	// --------------------------------------------------------------------
	control_merge_cross: cross merge_valid_cp, enable_cp, last_frame_cp;
	control_resolve_cross: cross resolve_valid_cp, enable_cp, last_frame_cp;

	merge_resolve_same_frame_cross: cross merge_valid_cp, resolve_valid_cp, last_frame_cp {
	  bins both_ops_midframe = binsof(merge_valid_cp.merge_request) &&
							   binsof(resolve_valid_cp.resolve_request) &&
							   binsof(last_frame_cp.mid_frame);

	  bins both_ops_at_end = binsof(merge_valid_cp.merge_request) &&
							 binsof(resolve_valid_cp.resolve_request) &&
							 binsof(last_frame_cp.end_frame);

	  bins merge_only_midframe = binsof(merge_valid_cp.merge_request) &&
								 binsof(resolve_valid_cp.no_resolve_request) &&
								 binsof(last_frame_cp.mid_frame);

	  bins resolve_only_midframe = binsof(merge_valid_cp.no_merge_request) &&
								   binsof(resolve_valid_cp.resolve_request) &&
								   binsof(last_frame_cp.mid_frame);
	}

  endgroup

  cg_lm lm_coverage = new();

endmodule
