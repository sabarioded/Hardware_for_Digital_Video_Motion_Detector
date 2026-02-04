/*------------------------------------------------------------------------------
 * File          : mp_seuencer.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jun 11, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mp_sequencer extends uvm_sequencer#(mp_trans);
	`uvm_component_utils(mp_sequencer)
	
	function new(string name = "mp_sequencer", uvm_component parent = null);
	  super.new(name, parent);
	endfunction
	
endclass