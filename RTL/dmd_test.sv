/*------------------------------------------------------------------------------
 * File          : dmd_test.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jul 6, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class dmd_test extends uvm_test;
	`uvm_component_utils(dmd_test)

	dmd_env  env;

	function new(string name = "dmd_test", uvm_codmdonent parent = null);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  env = dmd_env::type_id::create("env", this);
	endfunction

	task run_phase(uvm_phase phase);
	  dmd_sequence seq;

	  phase.raise_objection(this);

	  // Create and start sequence with context
	  seq = dmd_sequence::type_id::create("seq", this);
	  seq.start(env.agent.seqr);
	  phase.drop_objection(this);
	endtask

endclass