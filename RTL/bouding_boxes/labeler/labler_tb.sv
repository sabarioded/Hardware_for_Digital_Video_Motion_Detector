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

covergroup cg_labler @(posedge vif.clk);
  option.per_instance = 1;

  // control signals
  rst_cp:           coverpoint vif.rst              { bins active = {1}; bins inactive = {0}; }
  enable_cp:        coverpoint vif.enable           { bins on     = {1}; bins off      = {0}; }
  motion_pixel_cp:  coverpoint vif.motion_pixel     { bins motion = {1}; bins no_motion = {0}; }

  left_label_cp: coverpoint vif.left_label {
	bins min    = {0};
	bins range1 = {[1:85]};
	bins range2 = {[86:170]};
	bins range3 = {[171:254]};
	bins max    = {255};
  }
  top_label_cp: coverpoint vif.top_label {
	bins min    = {0};
	bins range1 = {[1:85]};
	bins range2 = {[86:170]};
	bins range3 = {[171:254]};
	bins max    = {255};
  }

  new_label_value_cp: coverpoint vif.new_label_value {
	bins min    = {0};
	bins range1 = {[1:85]};
	bins range2 = {[86:170]};
	bins range3 = {[171:254]};
	bins max    = {255};
  }
  new_label_valid_cp: coverpoint vif.new_label_valid { bins alloc = {1}; bins no_alloc = {0}; }

  merge_labels_cp: coverpoint vif.merge_labels { bins do_merge = {1}; bins no_merge = {0}; }
  merge_a_cp: coverpoint vif.merge_a {
	bins range1 = {[1:85]};
	bins range2 = {[86:170]};
	bins range3 = {[171:255]};
  }
  merge_b_cp: coverpoint vif.merge_b {
	bins range1 = {[1:85]};
	bins range2 = {[86:170]};
	bins range3 = {[171:254]};
	bins max    = {255};
  }

  current_label_cp: coverpoint vif.current_label {
	bins min    = {0};
	bins range1 = {[1:85]};
	bins range2 = {[86:170]};
	bins range3 = {[171:254]};
	bins max    = {255};
  }

  // cross-coverage
  neighbor_cross: cross left_label_cp, top_label_cp;
endgroup

// Instantiate and sample coverage
cg_labler labler_coverage = new();

endmodule
