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
  .clk             (vif.clk),
  .rst             (vif.rst),
  .enable          (vif.enable),
  .motion_pixel    (vif.motion_pixel),
  .last_in_frame      (vif.last_in_frame),
  .rgb_pixel	(vif.rbg_pixel),
  .width       (vif.width),
  .height (vif.height),
  .pixel_valid	(vif.pixel_valid),
  .highlighted_pixel	(vif.highlighted_pixel),
  .x_out		(vif.x_out),
  .y_out		(vif.y_out)
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

covergroup cg_bbox @(posedge vif.clk);
  option.per_instance = 1;

  // control signals
  rst_cp:           coverpoint vif.rst              { bins active = {1}; bins inactive = {0}; }
  enable_cp:        coverpoint vif.enable           { bins on     = {1}; bins off      = {0}; }
  motion_pixel_cp:  coverpoint vif.motion_pixel     { bins motion = {1}; bins no_motion = {0}; }
  last_in_frame_cp:  coverpoint vif.last_in_frame     { bins last_Frame = {1}; bins no_last_Frame = {0}; }
  


endgroup

// Instantiate and sample coverage
cg_bbox bbox_coverage = new();

endmodule
