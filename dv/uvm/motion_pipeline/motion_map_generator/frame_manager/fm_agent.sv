/*------------------------------------------------------------------------------
 * File          : fm_agent.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 15, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class fm_agent extends uvm_agent;
	`uvm_component_utils(fm_agent)

	// Components
	fm_driver      driver;
	fm_monitor     monitor;
	fm_sequencer   seqr;

	// Analysis port for communication with the scoreboard
	uvm_analysis_port#(fm_trans) ap;

	function new(string name = "fm_agent", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  driver = fm_driver::type_id::create("driver", this);
	  monitor = fm_monitor::type_id::create("monitor", this);
	  seqr    = fm_sequencer::type_id::create("seqr", this);
	  ap      = new("ap", this);
	endfunction

	function void connect_phase(uvm_phase phase);
	  super.connect_phase(phase);
	  driver.seq_item_port.connect(seqr.seq_item_export);
	  monitor.ap.connect(ap);
	endfunction

  endclass