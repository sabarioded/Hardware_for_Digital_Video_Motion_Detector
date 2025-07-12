/*------------------------------------------------------------------------------
 * File          : dmd_agent.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jul 6, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class dmd_agent extends uvm_agent;
	`uvm_component_utils(dmd_agent)
	
	//codmdonents
	dmd_sequencer seqr;
	dmd_driver driver;
	dmd_monitor monitor;
	
	// analysis port from monitor to scoreboard
	uvm_analysis_port#(dmd_trans) ap;
	
	// constructor
	function new(string name = "dmd_agent", uvm_codmdonent parent = null);
		super.new(name,parent);
	endfunction
	
	// build phase
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seqr = dmd_sequencer::type_id::create("seqr",this);
		driver = dmd_driver::type_id::create("driver",this);
		monitor = dmd_monitor::type_id::create("monitor",this);
		ap = new("ap",this);
	endfunction
	
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		//connect driver and sequencer
		driver.seq_item_port.connect(seqr.seq_item_export);
		
		// connect monitor to agent output
		monitor.ap_out.connect(ap);
	endfunction

endclass