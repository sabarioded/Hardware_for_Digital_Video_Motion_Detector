/*------------------------------------------------------------------------------
 * File          : labler_env.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 24, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class labler_env extends uvm_env;
  `uvm_component_utils(labler_env)

  // agent and scoreboard instances
  labler_agent       agent;
  labler_scoreboard  scoreboard;

  // constructor
  function new(string name = "labler_env", uvm_component parent = null);
	super.new(name, parent);
  endfunction: new

  // build phase: instantiate sub-components
  virtual function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	agent      = labler_agent::type_id::create("agent", this);
	scoreboard = labler_scoreboard::type_id::create("scoreboard", this);
  endfunction: build_phase

  // connect phase: wire analysis ports
  virtual function void connect_phase(uvm_phase phase);
	super.connect_phase(phase);
	// connect monitor analysis port to scoreboard
	agent.ap.connect(scoreboard.ap);
  endfunction: connect_phase

endclass: labler_env