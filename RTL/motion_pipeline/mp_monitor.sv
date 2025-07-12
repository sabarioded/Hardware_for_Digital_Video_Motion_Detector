/*------------------------------------------------------------------------------
 * File          : mp_monitor.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jun 11, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mp_monitor extends uvm_monitor;
	//factory
	`uvm_component_utils(mp_monitor)
	
	// interface
	virtual mp_if vif;
	
	// analysis ports
	uvm_analysis_port#(mp_trans) ap_out; // to scoreboard
	uvm_tlm_analysis_fifo#(mp_trans) ap_fifo;
	
	//constructor
	function new(string name = "mp_monitor", uvm_component parent = null);
		super.new(name,parent);
		ap_out = new("ap_out", this);
		ap_fifo = new("ap_fifo",this);
	endfunction
	
	// build phase - get the interface
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db#(virtual mp_if)::get(this,"","vif",vif))
		  `uvm_fatal("MONITOR","interface not found");
	endfunction
	
	// update the transaction in the run phase and send it to the scoreboard
	virtual task run_phase(uvm_phase phase);
		mp_trans tr;
		
		wait(!vif.rst);
		
		repeat(5) @(posedge vif.clk);
		
		forever begin
			while(ap_fifo.try_get(tr)) begin
				tr.highlighted_pixel = vif.highlighted_pixel;
				tr.pixel_valid = vif.pixel_valid;
				tr.pixel_last 	= vif.pixel_last;

				//`uvm_info(get_type_name(),
					//	$sformatf("Monitor: enable=%0d, rbg_pixel=0x%0d, last_in_frame=%0d, highlighted_pixel=%0d, pixel_valid=%0d", 
						//		  tr.enable, tr.rbg_pixel, tr.last_in_frame, tr.highlighted_pixel, tr.pixel_valid),
						//UVM_MEDIUM);
				
				ap_out.write(tr);
				@(posedge vif.clk);
			end
		end
	endtask
	
endclass