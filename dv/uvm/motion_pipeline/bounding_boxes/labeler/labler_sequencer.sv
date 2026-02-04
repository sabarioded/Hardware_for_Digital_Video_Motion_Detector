/*------------------------------------------------------------------------------
 * File          : labler_sequencer.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 23, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class labler_sequencer extends uvm_sequencer#(labler_trans);
	`uvm_component_utils(labler_sequencer)
	
	function new(string name = "labler_sequencer", uvm_component parent = null);
	  super.new(name, parent);
	endfunction
	
  endclass