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
  .width       (vif.width),
  .height (vif.height),
  .bbox_valid (vif.bbox_valid),
  .bbox_label    (vif.bbox_label),
  .bbox_parent 	(vif.bbox_parent),
  .bbox_min_x         (vif.bbox_min_x),
  .bbox_min_y         (vif.bbox_min_y),
  .bbox_max_x   (vif.bbox_max_x),
  .bbox_max_y   (vif.bbox_max_y)
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
  
  bbox_valid_cp:  coverpoint vif.bbox_valid     { bins valid_box = {1}; bins no_valid_boxes = {0}; }

  bbox_label_cp: coverpoint vif.bbox_label {
	bins min    = {0};
	bins range1 = {[1:85]};
	bins range2 = {[86:170]};
	bins range3 = {[171:254]};
	bins max    = {255};
  }
  bbox_min_x_cp: coverpoint vif.bbox_min_x {
	bins range1 = {[0:255]};
	bins range2 = {[256:511]};
	bins range3 = {[512:767]};
	bins range4 = {[768:1023]};
	bins range5 = {[1024:1279]};
  }
  bbox_min_y_cp: coverpoint vif.bbox_min_y {
	  bins range1 = {[0:143]};
	  bins range2 = {[144:287]};
	  bins range3 = {[288:431]};
	  bins range4 = {[432:575]};
	  bins range5 = {[576:719]};
	}
  bbox_max_x_cp: coverpoint vif.bbox_max_x {
	  bins range1 = {[0:255]};
	  bins range2 = {[256:511]};
	  bins range3 = {[512:767]};
	  bins range4 = {[768:1023]};
	  bins range5 = {[1024:1279]};
	}
	bbox_max_y_cp: coverpoint vif.bbox_max_y {
		bins range1 = {[0:143]};
		bins range2 = {[144:287]};
		bins range3 = {[288:431]};
		bins range4 = {[432:575]};
		bins range5 = {[576:719]};
	  }

endgroup

// Instantiate and sample coverage
cg_bbox bbox_coverage = new();

endmodule
