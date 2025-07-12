/*------------------------------------------------------------------------------
 * File          : mp_agent.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jun 11, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mp_agent extends uvm_agent;
	`uvm_component_utils(mp_agent)
	
	//components
	mp_sequencer seqr;
	mp_driver driver;
	mp_monitor monitor;
	
	// analysis port from monitor to scoreboard
	uvm_analysis_port#(mp_trans) ap;
	
	// constructor
	function new(string name = "mp_agent", uvm_component parent = null);
		super.new(name,parent);
	endfunction
	
	// build phase
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seqr = mp_sequencer::type_id::create("seqr",this);
		driver = mp_driver::type_id::create("driver",this);
		monitor = mp_monitor::type_id::create("monitor",this);
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