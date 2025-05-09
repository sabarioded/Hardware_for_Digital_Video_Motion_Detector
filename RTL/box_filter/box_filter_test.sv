/*------------------------------------------------------------------------------
 * File          : box_filter_test.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class box_filter_test extends uvm_test;
	`uvm_component_utils(box_filter_test)

	box_filter_env  env;

	function new(string name = "box_filter_test", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  env = box_filter_env::type_id::create("env", this);
	endfunction

	task run_phase(uvm_phase phase);
		box_filter_sequence seq;

	  phase.raise_objection(this);

	  // Create and start sequence with context
	  seq = box_filter_sequence::type_id::create("seq", this);
	  seq.start(env.agent.seqr);
	  
	  phase.drop_objection(this);
	endtask

  endclass
