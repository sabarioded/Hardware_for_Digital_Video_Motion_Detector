/*------------------------------------------------------------------------------
 * File          : lm_tb.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 26, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module lm_tb;
import uvm_pkg::*;
`include "uvm_macros.svh"

lm_if vif();

label_merger dut(
  .clk             (vif.clk),
  .rst             (vif.rst),
  .enable          (vif.enable),
  .merge_valid    (vif.merge_valid),
  .merge_a      (vif.merge_a),
  .merge_b       (vif.merge_b),
  .resolve_valid (vif.resolve_valid),
  .resolve_label (vif.resolve_label),
  .resolved_label    (vif.resolved_label)
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
  uvm_config_db#(virtual lm_if)::set(null, "*", "vif", vif);
  run_test("lm_test");
end

covergroup cg_lm @(posedge vif.clk);
  option.per_instance = 1;

  // control signals
  rst_cp:           coverpoint vif.rst              { bins active = {1}; bins inactive = {0}; }
  enable_cp:        coverpoint vif.enable           { bins on     = {1}; bins off      = {0}; }
  merge_valid_cp:  coverpoint vif.merge_valid     { bins merge = {1}; bins no_merge = {0}; }

  merge_a_cp: coverpoint vif.merge_a {
	bins min    = {0};
	bins range1 = {[1:85]};
	bins range2 = {[86:170]};
	bins range3 = {[171:254]};
	bins max    = {255};
  }
  merge_b_cp: coverpoint vif.merge_b {
	bins min    = {0};
	bins range1 = {[1:85]};
	bins range2 = {[86:170]};
	bins range3 = {[171:254]};
	bins max    = {255};
  }
  
  resolve_valid_cp: coverpoint vif.resolve_valid {bins resolve = {1}; bins no_resolve = {0}; }
 
  resolve_label_cp: coverpoint vif.resolve_label {
	bins min    = {0};
	bins range1 = {[1:85]};
	bins range2 = {[86:170]};
	bins range3 = {[171:254]};
	bins max    = {255};
  }

  resolved_label_cp: coverpoint vif.resolved_label {
	  bins min    = {0};
	  bins range1 = {[1:85]};
	  bins range2 = {[86:170]};
	  bins range3 = {[171:254]};
	  bins max    = {255};
  }
  
endgroup

// Instantiate and sample coverage
cg_lm lm_coverage = new();

endmodule
