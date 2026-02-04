/*------------------------------------------------------------------------------
 * File          : lm_sequencer.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 26, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class lm_sequencer extends uvm_sequencer#(lm_trans);
	`uvm_component_utils(lm_sequencer)
	
	function new(string name = "lm_sequencer", uvm_component parent = null);
	  super.new(name, parent);
	endfunction
	
  endclass