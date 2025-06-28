/*------------------------------------------------------------------------------
 * File          : mmg_env.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 17, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mmg_env extends uvm_env;
	`uvm_component_utils(mmg_env)

	// Agent and scoreboard
	mmg_agent         agent;
	mmg_scoreboard  scoreboard;

	// Constructor
	function new(string name = "mmg_env", uvm_component parent = null);
	  super.new(name, parent);
	endfunction: new

	//----------------------------------------------------------------------
	// Build phase: create components
	//----------------------------------------------------------------------
	virtual function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  agent      = mmg_agent::type_id::create("agent", this);
	  scoreboard = mmg_scoreboard::type_id::create("scoreboard", this);
	endfunction: build_phase

	//----------------------------------------------------------------------
	// Connect phase: hook up agent to scoreboard
	//----------------------------------------------------------------------
	virtual function void connect_phase(uvm_phase phase);
	  super.connect_phase(phase);
	  agent.ap_out.connect(scoreboard.ap_in);
	endfunction: connect_phase

  endclass: mmg_env
