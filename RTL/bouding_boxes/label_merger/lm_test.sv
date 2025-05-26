/*------------------------------------------------------------------------------
 * File          : lm_test.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 26, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class lm_test extends uvm_test;
	`uvm_component_utils(lm_test)

	lm_env  env;

	function new(string name = "lm_test", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  env = lm_env::type_id::create("env", this);
	endfunction

	task run_phase(uvm_phase phase);
	  lm_sequence seq;

	  phase.raise_objection(this);

	  // Create and start sequence with context
	  seq = lm_sequence::type_id::create("seq", this);
	  seq.start(env.agent.seqr);
	  
	  phase.drop_objection(this);
	endtask

endclass