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
		
		repeat(4) @(posedge vif.clk);
		
		forever begin
			while(ap_fifo.try_get(tr)) begin
				tr.pixel_valid = vif.pixel_valid;
				tr.highlighted_pixel = vif.highlighted_pixel;
				tr.x    = vif.x_out;
				tr.y         = vif.y_out;
				//`uvm_info(get_type_name(),
					//	$sformatf("Monitor: enable=%0d, motion_pixel=0x%0d, last_in_frame=%0d, x=%0d, y=%0d", 
						//		  tr.enable, tr.motion_pixel, tr.last_in_frame, tr.x, tr.y),
						//UVM_MEDIUM);
				
				ap_out.write(tr);
				@(posedge vif.clk);
			end
		end
	endtask
	
endclass