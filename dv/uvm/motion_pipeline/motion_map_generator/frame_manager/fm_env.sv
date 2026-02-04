/*------------------------------------------------------------------------------
 * File          : fm_env.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 15, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class fm_env extends uvm_env;
	`uvm_component_utils(fm_env)

	// Agent and scoreboard
	fm_agent         agent;
	fm_scoreboard  scoreboard;

	// Constructor
	function new(string name = "fm_env", uvm_component parent = null);
	  super.new(name, parent);
	endfunction: new

	//----------------------------------------------------------------------
	// Build phase: create components
	//----------------------------------------------------------------------
	virtual function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  agent      = fm_agent::type_id::create("agent", this);
	  scoreboard = fm_scoreboard::type_id::create("scoreboard", this);
	endfunction: build_phase

	//----------------------------------------------------------------------
	// Connect phase: hook up agent to scoreboard
	//----------------------------------------------------------------------
	virtual function void connect_phase(uvm_phase phase);
	  super.connect_phase(phase);
	  agent.ap.connect(scoreboard.ap);
	endfunction: connect_phase

  endclass: fm_env