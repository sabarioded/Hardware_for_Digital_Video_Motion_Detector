/*------------------------------------------------------------------------------
 * File          : labler_agent.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 23, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class labler_agent extends uvm_agent;
	`uvm_component_utils(labler_agent)
	
	//components
	labler_sequencer seqr;
	labler_driver driver;
	labler_monitor monitor;
	
	// analysis port from monitor to scoreboard
	uvm_analysis_port#(labler_trans) ap;
	
	// constructor
	function new(string name = "labler_agent", uvm_component parent = null);
		super.new(name,parent);
	endfunction
	
	// build phase
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seqr = labler_sequencer::type_id::create("seqr",this);
		driver = labler_driver::type_id::create("driver",this);
		monitor = labler_monitor::type_id::create("monitor",this);
		ap = new("ap",this);
	endfunction
	
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		//connect driver and sequencer
		driver.seq_item_port.connect(seqr.seq_item_export);
		
		//connect driver and monitor
		driver.ap.connect(monitor.ap_fifo.analysis_export);
		
		// connect monitor to agent output
		monitor.ap_out.connect(ap);
	endfunction
	
	
	
endclass