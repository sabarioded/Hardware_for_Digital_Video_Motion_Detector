/*------------------------------------------------------------------------------
 * File          : mmg_sequencer.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 17, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mmg_sequencer extends uvm_sequencer#(mmg_trans);
	`uvm_component_utils(mmg_sequencer)
	
	function new(string name = "mmg_sequencer", uvm_component parent = null);
	  super.new(name, parent);
	endfunction
	
  endclass