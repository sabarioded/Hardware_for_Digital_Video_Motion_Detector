/*------------------------------------------------------------------------------
 * File          : fm_sequencer.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 15, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class fm_sequencer extends uvm_sequencer#(fm_trans);
	`uvm_component_utils(fm_sequencer)
	
	function new(string name = "fm_sequencer", uvm_component parent = null);
	  super.new(name, parent);
	endfunction
	
  endclass
