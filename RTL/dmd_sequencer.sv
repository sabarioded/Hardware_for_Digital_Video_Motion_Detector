/*------------------------------------------------------------------------------
 * File          : dmd_sequencer.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jul 6, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class dmd_sequencer extends uvm_sequencer#(dmd_trans);
	`uvm_component_utils(dmd_sequencer)
	
	function new(string name = "dmd_sequencer", uvm_component parent = null);
	  super.new(name, parent);
	endfunction
	
  endclass