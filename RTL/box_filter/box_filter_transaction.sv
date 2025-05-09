/*------------------------------------------------------------------------------
 * File          : box_filter_transaction.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class box_filter_transaction extends uvm_sequence_item;

	// Input
	rand logic        enable;
	rand logic [3:0]  neighbors_number;
	rand logic [8:0]  motion_map;

	// Output
	logic            filtered_motion;

	`uvm_object_utils(box_filter_transaction)

	function new(string name = "box_filter_transaction");
		super.new(name);
	endfunction
	
	// Ensure we never exceed 8 neighbors (in 3x3 window)
	constraint neighbor_num {
		neighbors_number inside {[0:8]};
	}

endclass
