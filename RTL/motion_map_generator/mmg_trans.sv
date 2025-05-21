/*------------------------------------------------------------------------------
 * File          : mmg_trans.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 17, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mmg_trans extends uvm_sequence_item;
	//input
	rand logic enable;
	rand logic last_in_frame;
	rand logic wr_background;
	rand logic [7:0] threshold;
	rand logic [31:0] pixel;
	// placeholder for output
	logic motion_detected;
	
	`uvm_object_utils(mmg_trans)
	
	function new(string name = "mmg_trans");
		super.new(name);
	endfunction
endclass