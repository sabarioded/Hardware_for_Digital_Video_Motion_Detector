/*------------------------------------------------------------------------------
 * File          : bbox_exp_trans.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 27, 2025
 * Description   : "Expected" transaction for bounding box (used by sequence and scoreboard)
 *------------------------------------------------------------------------------*/

class bbox_exp_trans extends uvm_sequence_item;
  `uvm_object_utils(bbox_exp_trans)

  localparam WIDTH_BITS  = 11;
  localparam HEIGHT_BITS = 10;
  localparam LABEL_WIDTH = 8;
  // Bounding-box fields
  bit [WIDTH_BITS-1:0]       bbox_min_x;
  bit [HEIGHT_BITS-1:0]      bbox_min_y;
  bit [WIDTH_BITS-1:0]       bbox_max_x;
  bit [HEIGHT_BITS-1:0]      bbox_max_y;

  // Standard UVM methods
  function new(string name = "bbox_exp_trans");
	super.new(name);
	// initialize default values
	bbox_min_x = '0;
	bbox_min_y = '0;
	bbox_max_x = '0;
	bbox_max_y = '0;
  endfunction

endclass: bbox_exp_trans
