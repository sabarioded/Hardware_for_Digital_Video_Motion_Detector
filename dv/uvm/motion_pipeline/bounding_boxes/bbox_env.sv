/*------------------------------------------------------------------------------
 * File          : bbox_env.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 27, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class bbox_env extends uvm_env;
  `uvm_component_utils(bbox_env)

  // agent and scoreboard instances
  bbox_agent       agent;
  bbox_scoreboard  scoreboard;

  // constructor
  function new(string name = "bbox_env", uvm_component parent = null);
	super.new(name, parent);
  endfunction: new

  // build phase: instantiate sub-components
  virtual function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	agent      = bbox_agent::type_id::create("agent", this);
	scoreboard = bbox_scoreboard::type_id::create("scoreboard", this);
  endfunction: build_phase

  // connect phase: wire analysis ports
  virtual function void connect_phase(uvm_phase phase);
	super.connect_phase(phase);
	// connect monitor analysis port to scoreboard
	agent.dut_ap.connect(scoreboard.dut_imp);
	agent.exp_ap.connect(scoreboard.expected_imp);
  endfunction: connect_phase

endclass: bbox_env