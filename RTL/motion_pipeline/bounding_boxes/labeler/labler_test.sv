/*------------------------------------------------------------------------------
 * File          : labler_test.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 24, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class labler_test extends uvm_test;
	`uvm_component_utils(labler_test)

	labler_env  env;

	function new(string name = "labler_test", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  env = labler_env::type_id::create("env", this);
	endfunction

	task run_phase(uvm_phase phase);
	  labler_sequence seq;

	  phase.raise_objection(this);

	  // Create and start sequence with context
	  seq = labler_sequence::type_id::create("seq", this);
	  seq.start(env.agent.seqr);
	  
	  phase.drop_objection(this);
	endtask

endclass