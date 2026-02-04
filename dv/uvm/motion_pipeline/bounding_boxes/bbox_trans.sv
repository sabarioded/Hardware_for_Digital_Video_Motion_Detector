/*------------------------------------------------------------------------------
 * File          : bbox_trans.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 27, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class bbox_trans extends uvm_sequence_item;
	localparam WIDTH_BITS  = 11;
	localparam HEIGHT_BITS = 10;
	localparam LABEL_WIDTH = 8;
	
	rand  logic                         enable;

	// Streaming input
	rand  logic                         motion_pixel;
	rand  logic                         last_in_frame;
	rand logic [31:0] 		rbg_pixel;
	// Configuration data. should be constant.
	rand  logic [WIDTH_BITS-1:0]       width;
	rand  logic [HEIGHT_BITS-1:0]      height;
	
	// placeholder for outputs.
	logic [31:0] highlighted_pixel;
	logic pixel_valid;
	
	// DEBUG SIGNALS
	rand int frame_id;
	logic [WIDTH_BITS-1:0]  x;
	logic [HEIGHT_BITS-1:0] y;
	
	logic [LABEL_WIDTH-1:0]      bbox_label;
	logic [WIDTH_BITS-1:0]       bbox_min_x;
	logic [HEIGHT_BITS-1:0]      bbox_min_y;
	logic [WIDTH_BITS-1:0]       bbox_max_x;
	logic [HEIGHT_BITS-1:0]      bbox_max_y;
	// END DEBUG
	
	`uvm_object_utils(bbox_trans)
	
	function new(string name = "bbox_trans");
		super.new(name);
	endfunction
	
endclass