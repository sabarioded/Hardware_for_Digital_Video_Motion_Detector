/*------------------------------------------------------------------------------
 * File          : bbox_sequencer.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 27, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class bbox_sequencer extends uvm_sequencer#(bbox_trans);
	`uvm_component_utils(bbox_sequencer)
	
	uvm_analysis_port#(bbox_trans) exp;
	function new(string name = "bbox_sequencer", uvm_component parent = null);
	  super.new(name, parent);
	  exp = new("exp",this);
	endfunction
	
  endclass