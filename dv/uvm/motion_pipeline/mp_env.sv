/*------------------------------------------------------------------------------
 * File          : mp_env.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jun 11, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mp_env extends uvm_env;
  `uvm_component_utils(mp_env)

  // agent and scoreboard instances
  mp_agent       agent;
  mp_scoreboard  scoreboard;

  // constructor
  function new(string name = "mp_env", uvm_component parent = null);
	super.new(name, parent);
  endfunction: new

  // build phase: instantiate sub-components
  virtual function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	agent      = mp_agent::type_id::create("agent", this);
	scoreboard = mp_scoreboard::type_id::create("scoreboard", this);
  endfunction: build_phase

  // connect phase: wire analysis ports
  virtual function void connect_phase(uvm_phase phase);
	super.connect_phase(phase);
	// connect monitor analysis port to scoreboard
	agent.ap.connect(scoreboard.ap);
  endfunction: connect_phase

endclass: mp_env