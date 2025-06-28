/*------------------------------------------------------------------------------
 * File          : mp_trans.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jun 11, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mp_trans extends uvm_sequence_item;
	localparam WIDTH_BITS  = 11;
	localparam HEIGHT_BITS = 10;
	
	// input
	rand logic enable;
	rand logic [31:0] rbg_pixel;
	rand logic [31:0] memory_pixel;
	rand logic last_in_frame;
	rand logic [7:0] threshold;
	rand logic [WIDTH_BITS-1:0]  width;
	rand logic [HEIGHT_BITS-1:0] height;
	int frame_id;
	logic wr_background;
	
	// Output
	logic [31:0] highlighted_pixel;
	logic pixel_valid;
	
	`uvm_object_utils(mp_trans)
	
	function new(string name = "mp_trans");
		super.new(name);
	endfunction
	
endclass