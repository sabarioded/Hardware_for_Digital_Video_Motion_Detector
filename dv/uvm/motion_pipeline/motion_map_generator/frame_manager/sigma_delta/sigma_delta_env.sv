/*------------------------------------------------------------------------------
 * File         : sigma_delta_environment.sv
 * Project      : RTL
 * Description  : Environment for sigma_delta_update module
 *------------------------------------------------------------------------------*/
class sigma_delta_env extends uvm_env;
	`uvm_component_utils(sigma_delta_env)

	sigma_delta_agent       agent;
	sigma_delta_scoreboard  scoreboard;

	function new(string name, uvm_component parent);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  agent      = sigma_delta_agent::type_id::create("agent", this);
	  scoreboard = sigma_delta_scoreboard::type_id::create("scoreboard", this);
	endfunction

	function void connect_phase(uvm_phase phase);
	  super.connect_phase(phase);
	  agent.ap.connect(scoreboard.ap); // Route data to scoreboard
	endfunction
  endclass
