/*------------------------------------------------------------------------------
 * File          : box_filter_sequencer.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class box_filter_sequencer extends uvm_sequencer#(box_filter_transaction);
	`uvm_component_utils(box_filter_sequencer)

	function new(string name = "box_filter_sequencer", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

  endclass