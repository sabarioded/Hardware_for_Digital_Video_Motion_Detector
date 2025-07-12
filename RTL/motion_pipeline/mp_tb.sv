/*------------------------------------------------------------------------------
 * File          : mp_tb.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jun 11, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module mp_tb;
import uvm_pkg::*;
`include "uvm_macros.svh"

mp_if vif();

motion_pipeline dut(
  .clk             (vif.clk),
  .rst             (vif.rst),
  .enable          (vif.enable),
  .rbg_pixel    (vif.rbg_pixel),
  .memory_pixel (vif.memory_pixel),
  .last_in_frame      (vif.last_in_frame),
  .wr_background    (vif.wr_background),
  .threshold	(vif.threshold),
  .width       (vif.width),
  .height (vif.height),
  .highlighted_pixel	(vif.highlighted_pixel),
  .pixel_valid	(vif.pixel_valid),
  .pixel_last 	(vif.pixel_last)
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
  uvm_config_db#(virtual mp_if)::set(null, "*", "vif", vif);
  run_test("mp_test");
end

endmodule
