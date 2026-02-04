/*------------------------------------------------------------------------------
 * File          : motion_detector_transaction.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class motion_detector_transaction extends uvm_sequence_item;

	// Input
	rand logic        enable;
	rand logic [7:0]  background;
	rand logic [7:0]  variance;
	rand logic [7:0]  curr_pixel;
	rand logic [7:0]  prev_pixel;
	rand logic [7:0]  threshold;

	// Output
	logic            motion_detected;

	`uvm_object_utils(motion_detector_transaction)

	function new(string name = "motion_detector_transaction");
		super.new(name);
	endfunction
	
	constraint valid_values {
		variance inside {[2:255]};
	}

endclass

