/*------------------------------------------------------------------------------
 * File          : lm_agent.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 26, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class lm_agent extends uvm_agent;
	`uvm_component_utils(lm_agent)
	
	//components
	lm_sequencer seqr;
	lm_driver driver;
	lm_monitor monitor;
	
	// analysis port from monitor to scoreboard
	uvm_analysis_port#(lm_trans) ap;
	
	// constructor
	function new(string name = "lm_agent", uvm_component parent = null);
		super.new(name,parent);
	endfunction
	
	// build phase
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seqr = lm_sequencer::type_id::create("seqr",this);
		driver = lm_driver::type_id::create("driver",this);
		monitor = lm_monitor::type_id::create("monitor",this);
		ap = new("ap",this);
	endfunction
	
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		//connect driver and sequencer
		driver.seq_item_port.connect(seqr.seq_item_export);
		
		//connect driver and monitor
		driver.ap.connect(monitor.fifo.analysis_export);
		
		// connect monitor to agent output
		monitor.ap.connect(ap);
	endfunction

endclass