/*------------------------------------------------------------------------------
 * File          : dmd_env.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jul 6, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class dmd_env extends uvm_env;
  `uvm_component_utils(dmd_env)

  // agent and scoreboard instances
  dmd_agent       agent;
  dmd_scoreboard  scoreboard;

  // constructor
  function new(string name = "dmd_env", uvm_codmdonent parent = null);
	super.new(name, parent);
  endfunction: new

  // build phase: instantiate sub-codmdonents
  virtual function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	agent      = dmd_agent::type_id::create("agent", this);
	scoreboard = dmd_scoreboard::type_id::create("scoreboard", this);
  endfunction: build_phase

  // connect phase: wire analysis ports
  virtual function void connect_phase(uvm_phase phase);
	super.connect_phase(phase);
	// connect monitor analysis port to scoreboard
	agent.ap.connect(scoreboard.ap);
  endfunction: connect_phase

endclass: dmd_env