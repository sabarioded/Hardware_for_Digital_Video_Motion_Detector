/*------------------------------------------------------------------------------
 * File          : labler_monitor.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 23, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class labler_monitor extends uvm_monitor;
	//factory
	`uvm_component_utils(labler_monitor)
	
	// interface
	virtual labler_if vif;
	
	// analysis ports
	uvm_analysis_port#(labler_trans) ap_out; // to scoreboard
	uvm_tlm_analysis_fifo#(labler_trans) ap_fifo;
	
	//constructor
	function new(string name = "labler_monitor", uvm_component parent = null);
		super.new(name,parent);
		ap_out = new("ap_out", this);
		ap_fifo = new("ap_fifo",this);
	endfunction
	
	// build phase - get the interface
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db#(virtual labler_if)::get(this,"","vif",vif))
		  `uvm_fatal("MONITOR","interface not found");
	endfunction
	
	// update the transaction in the run phase and send it to the scoreboard
	virtual task run_phase(uvm_phase phase);
		labler_trans tr;
		
		wait(!vif.rst);
		
		repeat(3) @(posedge vif.clk);
		
		forever begin
			while(ap_fifo.try_get(tr)) begin
				`uvm_info(get_type_name(),
					  $sformatf("Monitor: enable=%0d, motion_pixel=0x%0d, left_label=%0d, top_label=%0d", 
								tr.enable, tr.motion_pixel, tr.left_label, tr.top_label),
					  UVM_MEDIUM);
				tr.new_label_valid = vif.new_label_valid;
				tr.new_label_value = vif.new_label_value;
				tr.merge_labels    = vif.merge_labels;
				tr.merge_a         = vif.merge_a;
				tr.merge_b         = vif.merge_b;
				tr.current_label   = vif.current_label;
				
				ap_out.write(tr);
				@(posedge vif.clk);
			end
		end
	endtask
	
	
	
endclass