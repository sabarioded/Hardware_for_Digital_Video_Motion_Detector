/*------------------------------------------------------------------------------
 * File          : mp_test.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jun 11, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mp_test extends uvm_test;
	`uvm_component_utils(mp_test)

	mp_env  env;

	function new(string name = "mp_test", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  env = mp_env::type_id::create("env", this);
	endfunction

	task run_phase(uvm_phase phase);
	  mp_sequence seq;

	  phase.raise_objection(this);

	  // Create and start sequence with context
	  seq = mp_sequence::type_id::create("seq", this);
	  seq.start(env.agent.seqr);
	  phase.drop_objection(this);
	endtask

endclass