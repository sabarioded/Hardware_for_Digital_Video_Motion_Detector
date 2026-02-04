/*------------------------------------------------------------------------------
 * File          : motion_detector_agent.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class motion_detector_agent extends uvm_agent;
	`uvm_component_utils(motion_detector_agent)

	// Components
	motion_detector_driver      driver;
	motion_detector_monitor     monitor;
	motion_detector_sequencer   seqr;

	// Analysis port for communication with the scoreboard
	uvm_analysis_port#(motion_detector_transaction) ap;

	function new(string name = "motion_detector_agent", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  driver = motion_detector_driver::type_id::create("driver", this);
	  monitor = motion_detector_monitor::type_id::create("monitor", this);
	  seqr    = motion_detector_sequencer::type_id::create("seqr", this);
	  ap      = new("ap", this);
	endfunction

	function void connect_phase(uvm_phase phase);
	  super.connect_phase(phase);
	  driver.seq_item_port.connect(seqr.seq_item_export);
	  monitor.ap.connect(ap);
	endfunction

endclass

