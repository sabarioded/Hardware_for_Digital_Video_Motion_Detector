/*------------------------------------------------------------------------------
 * File          : motion_detector_test.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class motion_detector_test extends uvm_test;
	`uvm_component_utils(motion_detector_test)

	motion_detector_env  env;

	function new(string name = "motion_detector_test", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  env = motion_detector_env::type_id::create("env", this);
	endfunction

	task run_phase(uvm_phase phase);
	  motion_detector_sequence seq;

	  phase.raise_objection(this);

	  // Create and start sequence with context
	  seq = motion_detector_sequence::type_id::create("seq", this);
	  seq.start(env.agent.seqr);
	  
	  phase.drop_objection(this);
	endtask

  endclass
