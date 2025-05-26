/*------------------------------------------------------------------------------
 * File          : labler_trans.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 23, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class labler_trans extends uvm_sequence_item;
	localparam LABEL_WIDTH = 8;  // Supports up to 256 labels
	
	// Inputs
	rand bit enable;
	rand bit motion_pixel;
	rand bit [LABEL_WIDTH-1:0] left_label;
	rand bit [LABEL_WIDTH-1:0] top_label;
	
	// Outputs
	logic               new_label_valid;
	logic [LABEL_WIDTH-1:0] new_label_value;

	logic               merge_labels;
	logic [LABEL_WIDTH-1:0] merge_a;
	logic [LABEL_WIDTH-1:0] merge_b;

	logic [LABEL_WIDTH-1:0] current_label;
	
	// Factory and constructor
	`uvm_object_utils(labler_trans)
	
	function new(string name = "labler_trans");
		super.new(name);
	endfunction
	
endclass