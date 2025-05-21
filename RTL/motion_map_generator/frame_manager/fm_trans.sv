/*------------------------------------------------------------------------------
 * File          : fm_trans.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 15, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class fm_trans extends uvm_sequence_item;
	
	rand  logic enable;
	rand  logic [31:0] pixel;
	rand  logic        last_in_frame;

	logic [7:0]  curr_pixel;
	logic [7:0]  prev_pixel;
	
	rand logic    wr_background;
	logic [7:0] background_next;
	logic [7:0] variance_next;
	
	`uvm_object_utils(fm_trans)
	
	function new(string name = "fm_trans");
		super.new(name);
	endfunction
	
endclass