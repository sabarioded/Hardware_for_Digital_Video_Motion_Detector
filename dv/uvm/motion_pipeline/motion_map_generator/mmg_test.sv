/*------------------------------------------------------------------------------
 * File          : mmg_test.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 17, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mmg_test extends uvm_test;
	`uvm_component_utils(mmg_test)

	mmg_env  env;

	function new(string name = "mmg_test", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  env = mmg_env::type_id::create("env", this);
	endfunction

	task run_phase(uvm_phase phase);
		mmg_sequence seq;

	  phase.raise_objection(this);

	  // Create and start sequence with context
	  seq = mmg_sequence::type_id::create("seq", this);
	  seq.start(env.agent.seqr);
	  
	  phase.drop_objection(this);
	endtask

endclass