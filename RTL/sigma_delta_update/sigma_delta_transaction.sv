/*------------------------------------------------------------------------------
 * File          : sigma_delta_update_sequence_item.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 5, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class sigma_delta_transaction extends uvm_sequence_item;
	//Inputs
	rand logic enable;
	rand logic wr_background;
	rand logic [7:0]  curr_pixel;
	rand  logic [7:0]  background;
	rand  logic [7:0]  variance;
	//Outputs
	logic [7:0]  background_next;
	logic [7:0]  variance_next;
	logic        motion_detected;
	
	`uvm_object_utils(sigma_delta_transaction)
	
	function new(string name = "sigma_delta_transaction");
		super.new(name);
	endfunction
	
	
endclass