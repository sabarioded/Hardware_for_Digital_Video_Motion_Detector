/*------------------------------------------------------------------------------
 * File          : mmg_agent.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 17, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mmg_agent extends uvm_agent;
	`uvm_component_utils(mmg_agent)

	// Components
	mmg_driver      driver;
	mmg_monitor     monitor;
	mmg_sequencer   seqr;

	// only one port goes out to the scoreboard
	uvm_analysis_port#(mmg_trans) ap_out;

	function new(string name = "mmg_agent", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  driver  = mmg_driver ::type_id::create("driver",  this);
	  monitor = mmg_monitor::type_id::create("monitor", this);
	  seqr    = mmg_sequencer::type_id::create("seqr",    this);
	  ap_out = new("ap_out", this);
	endfunction

	function void connect_phase(uvm_phase phase);
	  super.connect_phase(phase);

	  // sequence port
	  driver.seq_item_port.connect(seqr.seq_item_export);

	  // 1) driver  -> monitor
	  driver.ap.connect(monitor.fifo.analysis_export);

	  // 2) monitor -> agent
	  monitor.ap_out.connect(ap_out);

	endfunction

  endclass
