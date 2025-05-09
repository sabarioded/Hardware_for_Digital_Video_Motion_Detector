/*------------------------------------------------------------------------------
 * File          : box_filter_env.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class box_filter_env extends uvm_env;
	`uvm_component_utils(box_filter_env)

	box_filter_agent       agent;
	box_filter_scoreboard  scoreboard;

	function new(string name, uvm_component parent);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  agent      = box_filter_agent::type_id::create("agent", this);
	  scoreboard = box_filter_scoreboard::type_id::create("scoreboard", this);
	endfunction

	function void connect_phase(uvm_phase phase);
	  super.connect_phase(phase);
	  agent.ap.connect(scoreboard.ap); // Route data to scoreboard
	endfunction
  endclass
