/*------------------------------------------------------------------------------
 * File          : sigma_delta_test.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 5, 2025
 * Description   :
 *------------------------------------------------------------------------------*/
class sigma_delta_test extends uvm_test;
	`uvm_component_utils(sigma_delta_test)

	sigma_delta_env  env;

	function new(string name = "sigma_delta_test", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  env = sigma_delta_env::type_id::create("env", this);
	endfunction

	task run_phase(uvm_phase phase);
	  sigma_delta_sequence seq;

	  phase.raise_objection(this);

	  // Create and start sequence with context
	  seq = sigma_delta_sequence::type_id::create("seq", this);
	  seq.start(env.agent.seqr);

	  #100us; // optional wait
	  phase.drop_objection(this);
	endtask

  endclass
