/*------------------------------------------------------------------------------
 * File          : bbox_tb.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 27, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module bbox_tb;
import uvm_pkg::*;
`include "uvm_macros.svh"

bbox_if vif();

bbox_top dut(
  .clk                 (vif.clk),
  .rst                 (vif.rst),
  .enable              (vif.enable),
  .motion_pixel        (vif.motion_pixel),
  .last_in_frame       (vif.last_in_frame),
  .rgb_pixel           (vif.rbg_pixel),
  .width               (vif.width),
  .height              (vif.height),
  .pixel_valid         (vif.pixel_valid),
  .highlighted_pixel   (vif.highlighted_pixel),
  .x_out               (vif.x_out),
  .y_out               (vif.y_out)
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
  uvm_config_db#(virtual bbox_if)::set(null, "*", "vif", vif);
  run_test("bbox_test");
end

//---
// Coverage Group for Bounding Box Top Module
//---
covergroup cg_bbox @(posedge vif.clk);
	option.per_instance = 1;
	option.name = "bbox_top_coverage";

	// --------------------------------------------------
	// 1. Basic Control Signals
	// --------------------------------------------------
	enable_cp: coverpoint vif.enable { bins on={1}; bins off={0}; }
	motion_pixel_cp: coverpoint vif.motion_pixel { bins motion={1}; bins no_motion={0}; }
	last_in_frame_cp: coverpoint vif.last_in_frame { bins last_frame={1}; bins mid_frame={0}; }
	pixel_valid_cp: coverpoint vif.pixel_valid { bins valid={1}; bins invalid={0}; }
	
	// --------------------------------------------------
	// 2. Coordinate Coverage (Frame exploration)
	// --------------------------------------------------
	x_coord_cp: coverpoint vif.x_out iff (vif.enable && !vif.rst) {
	  bins start_x = {0};
	  bins mid_x[] = {[1:vif.width-2]};
	  bins end_x   = {vif.width-1};
	}

	y_coord_cp: coverpoint vif.y_out iff (vif.enable && !vif.rst) {
	  bins start_y = {0};
	  bins mid_y[] = {[1:vif.height-2]};
	  bins end_y   = {vif.height-1};
	}

	xy_cross: cross x_coord_cp, y_coord_cp {
	  bins top_left_corner       = binsof(x_coord_cp.start_x) && binsof(y_coord_cp.start_y);
	  bins bottom_right_corner   = binsof(x_coord_cp.end_x)   && binsof(y_coord_cp.end_y);
	  bins frame_edges           = binsof(x_coord_cp.start_x) || binsof(x_coord_cp.end_x) ||
									binsof(y_coord_cp.start_y) || binsof(y_coord_cp.end_y);
	}

	// --------------------------------------------------
	// 3. FSM Coverage
	// --------------------------------------------------
	filter_state_cp: coverpoint dut.filter_state {
	  bins idle  = {dut.IDLE};
	  bins filter = {dut.FILTER};
	}

	output_state_cp: coverpoint dut.output_state {
	  bins idle_out   = {dut.IDLE_OUT};
	  bins filtering  = {dut.FILTERING};
	  bins outputing  = {dut.OUTPUTING};
	}

	// --------------------------------------------------
	// 4. Bank Switching Coverage
	// --------------------------------------------------
	bank_select_cp: coverpoint dut.bank_select {
	  bins bank0={0}; bins bank1={1}; bins bank2={2}; bins bank3={3};
	  // Cover bank transitions
	  bins bank_cycle = (0=>1, 1=>2, 2=>3, 3=>0) iff (vif.last_in_frame && vif.enable);
	}

	bank_role_cross: cross bank_select_cp, last_in_frame_cp;

	// --------------------------------------------------
	// 5. Bounding Box Lifecycle Coverage
	// --------------------------------------------------
	// Covers an initial activation for label 1 (can generalize with a genvar if needed)
	bbox_active_cp: coverpoint dut.banks[dut.input_bank_idx][1].label_active iff (vif.motion_pixel && vif.enable) {
	  bins activated   = {1};
	  bins inactive    = {0};
	}

	// Whether bbox gets merged (filter_bank activity)
	bbox_filter_merge_cp: coverpoint dut.banks[dut.filter_bank_idx][dut.merge_i].label_active iff (dut.filter_state==dut.FILTER && vif.enable) {
	  bins active_before_merge = {1};
	}

	bbox_deactivated_by_merge_cp: coverpoint dut.banks[dut.filter_bank_idx][dut.merge_j].label_active iff (dut.filter_state == dut.FILTER && vif.enable &&
									// Condition for merge to occur (from bbox_top logic)
									!(dut.banks[dut.filter_bank_idx][dut.merge_i].max_x + dut.PROX < dut.banks[dut.filter_bank_idx][dut.merge_j].min_x ||
									  dut.banks[dut.filter_bank_idx][dut.merge_i].min_x > dut.banks[dut.filter_bank_idx][dut.merge_j].max_x + dut.PROX ||
									  dut.banks[dut.filter_bank_idx][dut.merge_i].max_y + dut.PROX < dut.banks[dut.filter_bank_idx][dut.merge_j].min_y ||
									  dut.banks[dut.filter_bank_idx][dut.merge_i].min_y > dut.banks[dut.filter_bank_idx][dut.merge_j].max_y + dut.PROX)
									) {
		bins merged_and_deactivated = (1 => 0);
	}
	
	// --------------------------------------------------
	// 6. Highlighting Behavior
	// --------------------------------------------------
	on_any_bbox_edge_cp: coverpoint dut.on_any_bbox_edge {
	  bins edge_      = {1};
	  bins no_edge   = {0};
	}

	highlighted_pixel_cp: coverpoint vif.highlighted_pixel iff (vif.pixel_valid) {
	  bins edge_color    = {dut.HIGHLIGHT_COLOR};
	  bins normal_pixel  = default;
	}

	motion_highlight_cross: cross motion_pixel_cp, on_any_bbox_edge_cp {
	  bins motion_edge    = binsof(motion_pixel_cp.motion) && binsof(on_any_bbox_edge_cp.edge_);
	  bins motion_nonedge = binsof(motion_pixel_cp.motion) && binsof(on_any_bbox_edge_cp.no_edge);
	}

  endgroup


// Instantiate and sample coverage
cg_bbox bbox_coverage = new();

endmodule