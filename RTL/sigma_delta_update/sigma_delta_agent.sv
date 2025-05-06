/*------------------------------------------------------------------------------
 * File          : sigma_delta_agent.sv
 * Project       : RTL
 * Description   : Agent for sigma_delta_update UVM environment
 *------------------------------------------------------------------------------*/

class sigma_delta_agent extends uvm_agent;
  `uvm_component_utils(sigma_delta_agent)

  // Components
  sigma_delta_driver      driver;
  sigma_delta_monitor     monitor;
  sigma_delta_sequencer   seqr;

  // Analysis port for communication with the scoreboard
  uvm_analysis_port#(sigma_delta_transaction) ap;

  function new(string name = "sigma_delta_agent", uvm_component parent = null);
	super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	driver = sigma_delta_driver::type_id::create("driver", this);
	monitor = sigma_delta_monitor::type_id::create("monitor", this);
	seqr    = sigma_delta_sequencer::type_id::create("seqr", this);
	ap      = new("ap", this);
  endfunction

  function void connect_phase(uvm_phase phase);
	super.connect_phase(phase);
	driver.seq_item_port.connect(seqr.seq_item_export);
	monitor.ap.connect(ap);
  endfunction

endclass
