/*------------------------------------------------------------------------------
 * File          : bbox_monitor.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 27, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class bbox_monitor extends uvm_monitor;
	//factory
	`uvm_component_utils(bbox_monitor)
	
	// interface
	virtual bbox_if vif;
	
	// analysis ports
	uvm_analysis_port#(bbox_trans) ap_out; // to scoreboard
	uvm_tlm_analysis_fifo#(bbox_trans) ap_fifo;
	
	//constructor
	function new(string name = "bbox_monitor", uvm_component parent = null);
		super.new(name,parent);
		ap_out = new("ap_out", this);
		ap_fifo = new("ap_fifo",this);
	endfunction
	
	// build phase - get the interface
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db#(virtual bbox_if)::get(this,"","vif",vif))
		  `uvm_fatal("MONITOR","interface not found");
	endfunction
	
	// update the transaction in the run phase and send it to the scoreboard
	virtual task run_phase(uvm_phase phase);
		bbox_trans tr;
		
		wait(!vif.rst);
		
		repeat(3) @(posedge vif.clk);
		
		forever begin
			while(ap_fifo.try_get(tr)) begin
				//`uvm_info(get_type_name(),
					//  $sformatf("Monitor: enable=%0d, motion_pixel=0x%0d, last_in_frame=%0d", 
						//		tr.enable, tr.motion_pixel, tr.last_in_frame),
					  //UVM_MEDIUM);
				tr.bbox_valid = vif.bbox_valid;
				tr.bbox_label = vif.bbox_label;
				tr.bbox_parent = vif.bbox_parent;
				tr.bbox_min_x    = vif.bbox_min_x;
				tr.bbox_min_y         = vif.bbox_min_y;
				tr.bbox_max_x         = vif.bbox_max_x;
				tr.bbox_max_y   = vif.bbox_max_y;
				
				ap_out.write(tr);
				@(posedge vif.clk);
			end
		end
	endtask
	
endclass