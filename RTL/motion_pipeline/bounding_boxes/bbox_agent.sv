/*------------------------------------------------------------------------------
 * File          : bbox_agent.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 27, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class bbox_agent extends uvm_agent;
	`uvm_component_utils(bbox_agent)
	
	//components
	bbox_sequencer seqr;
	bbox_driver driver;
	bbox_monitor monitor;
	
	// analysis port from monitor to scoreboard
	uvm_analysis_port#(bbox_trans) dut_ap;
	uvm_analysis_port#(bbox_trans) exp_ap;
	
	// constructor
	function new(string name = "bbox_agent", uvm_component parent = null);
		super.new(name,parent);
	endfunction
	
	// build phase
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seqr = bbox_sequencer::type_id::create("seqr",this);
		driver = bbox_driver::type_id::create("driver",this);
		monitor = bbox_monitor::type_id::create("monitor",this);
		dut_ap = new("dut_ap",this);
		exp_ap = new("exp_ap",this);
	endfunction
	
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		//connect driver and sequencer
		driver.seq_item_port.connect(seqr.seq_item_export);
		
		//connect driver and monitor
		driver.ap.connect(monitor.ap_fifo.analysis_export);
		
		// connect monitor to agent output
		monitor.ap_out.connect(dut_ap);
		// connect sequence to agent output
		seqr.exp.connect(exp_ap);
	endfunction

endclass