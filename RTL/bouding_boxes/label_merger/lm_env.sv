/*------------------------------------------------------------------------------
 * File          : lm_env.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 26, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class lm_env extends uvm_env;
  `uvm_component_utils(lm_env)

  // agent and scoreboard instances
  lm_agent       agent;
  lm_scoreboard  scoreboard;

  // constructor
  function new(string name = "lm_env", uvm_component parent = null);
	super.new(name, parent);
  endfunction: new

  // build phase: instantiate sub-components
  virtual function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	agent      = lm_agent::type_id::create("agent", this);
	scoreboard = lm_scoreboard::type_id::create("scoreboard", this);
  endfunction: build_phase

  // connect phase: wire analysis ports
  virtual function void connect_phase(uvm_phase phase);
	super.connect_phase(phase);
	// connect monitor analysis port to scoreboard
	agent.ap.connect(scoreboard.ap);
  endfunction: connect_phase

endclass: lm_env