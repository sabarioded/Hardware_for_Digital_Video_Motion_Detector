/*------------------------------------------------------------------------------
 * File          : mmg_tb.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 17, 2025
 * Description   : UVM testbench for motion_map_generator
 *------------------------------------------------------------------------------*/
module mmg_tb;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Instantiate interface
  mmg_if vif();

  // Instantiate DUT
  motion_map_generator dut (
	.clk             (vif.clk),
	.rst             (vif.rst),
	.enable          (vif.enable),
	.pixel           (vif.pixel),
	.last_in_frame   (vif.last_in_frame),
	.wr_background   (vif.wr_background),
	.threshold       (vif.threshold),
	.motion_detected (vif.motion_detected)
  );

  // Clock generation: 100 MHz (~10 ns period)
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

  // UVM configuration and run
  initial begin
	uvm_config_db#(virtual mmg_if)::set(null, "*", "vif", vif);
	run_test("mmg_test");
  end

  //------------------------------------------------------------------------------
  // Functional coverage: covergroup sampling on clock edge
  //------------------------------------------------------------------------------
  covergroup cg_mmg @(posedge vif.clk);
	option.per_instance = 1;

	// Control signals
	rst_cp:           coverpoint vif.rst            { bins active   = {1}; bins inactive = {0}; }
	enable_cp:        coverpoint vif.enable         { bins on       = {1}; bins off      = {0}; }
	last_frame_cp:    coverpoint vif.last_in_frame  { bins start    = {1}; bins ongoing  = {0}; }
	wr_bg_cp:         coverpoint vif.wr_background  { bins write    = {1}; bins no_write = {0}; }

	// Pixel value (32-bit) in bins (LSB always 0)
	pixel_cp: coverpoint vif.pixel {
	  bins zero          = {32'h00000000};                        
	  bins quarter       = {[32'h00000100:32'h3FFFFF00]};         
	  bins half          = {[32'h40000000:32'h7FFFFF00]};         
	  bins three_quarter = {[32'h80000000:32'hBFFFFF00]};         
	  bins full          = {[32'hC0000000:32'hFFFFFE00]};         
	  bins max           = {32'hFFFFFF00};            
	}

	// Output detection
	motion_cp:       coverpoint vif.motion_detected { bins no = {0}; bins yes = {1}; }

  endgroup

  // Instantiate and sample coverage
  cg_mmg mmg_coverage;
  initial mmg_coverage = new();

endmodule : mmg_tb
