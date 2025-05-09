/*------------------------------------------------------------------------------
 * File          : box_filter_agent.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class box_filter_agent extends uvm_agent;
	`uvm_component_utils(box_filter_agent)

	// Components
	box_filter_driver      driver;
	box_filter_monitor     monitor;
	box_filter_sequencer   seqr;

	// Analysis port for communication with the scoreboard
	uvm_analysis_port#(box_filter_transaction) ap;

	function new(string name = "box_filter_agent", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  driver = box_filter_driver::type_id::create("driver", this);
	  monitor = box_filter_monitor::type_id::create("monitor", this);
	  seqr    = box_filter_sequencer::type_id::create("seqr", this);
	  ap      = new("ap", this);
	endfunction

	function void connect_phase(uvm_phase phase);
	  super.connect_phase(phase);
	  driver.seq_item_port.connect(seqr.seq_item_export);
	  monitor.ap.connect(ap);
	endfunction

endclass
