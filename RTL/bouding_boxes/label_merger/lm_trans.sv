/*------------------------------------------------------------------------------
 * File          : lm_trans.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 26, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class lm_trans extends uvm_sequence_item; 
	localparam LABEL_WIDTH = 8;
	
	rand logic enable;
	
	// Merge interface from labeler
	rand logic                    merge_valid;
	rand logic [LABEL_WIDTH-1:0]  merge_a;
	rand logic [LABEL_WIDTH-1:0]  merge_b;

  // Label to resolve
	rand logic                     resolve_valid;
	rand logic [LABEL_WIDTH-1:0]  resolve_label;
	logic [LABEL_WIDTH-1:0]  resolved_label;
	
	`uvm_object_utils(lm_trans)
	
	function new(string name = "lm_trans");
		super.new(name);
	endfunction
	
endclass