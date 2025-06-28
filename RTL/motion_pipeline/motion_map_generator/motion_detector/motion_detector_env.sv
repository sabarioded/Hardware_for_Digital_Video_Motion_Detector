/*------------------------------------------------------------------------------
 * File          : motion_detector_env.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class motion_detector_env extends uvm_env;
	`uvm_component_utils(motion_detector_env)

	motion_detector_agent       agent;
	motion_detector_scoreboard  scoreboard;

	function new(string name, uvm_component parent);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  agent      = motion_detector_agent::type_id::create("agent", this);
	  scoreboard = motion_detector_scoreboard::type_id::create("scoreboard", this);
	endfunction

	function void connect_phase(uvm_phase phase);
	  super.connect_phase(phase);
	  agent.ap.connect(scoreboard.ap); // Route data to scoreboard
	endfunction
  endclass
