/*------------------------------------------------------------------------------
 * File          : fm_test.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 15, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class fm_test extends uvm_test;
	`uvm_component_utils(fm_test)

	fm_env  env;

	function new(string name = "fm_test", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  env = fm_env::type_id::create("env", this);
	endfunction

	task run_phase(uvm_phase phase);
		fm_sequence seq;

	  phase.raise_objection(this);

	  // Create and start sequence with context
	  seq = fm_sequence::type_id::create("seq", this);
	  seq.start(env.agent.seqr);
	  
	  phase.drop_objection(this);
	endtask

endclass