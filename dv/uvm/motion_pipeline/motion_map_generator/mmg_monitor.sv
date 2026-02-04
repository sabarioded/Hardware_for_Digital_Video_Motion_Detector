/*------------------------------------------------------------------------------
 * File          : mmg_monitor.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 17, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mmg_monitor extends uvm_monitor;
	`uvm_component_utils(mmg_monitor)
	
	virtual mmg_if                        vif;
	uvm_tlm_analysis_fifo#(mmg_trans)     fifo;    // buffer incoming trans
	uvm_analysis_port#(mmg_trans)         ap_out;  // send to scoreboard
	
	function new(string name="mmg_monitor", uvm_component parent=null);
	  super.new(name,parent);
	  fifo   = new("fifo",   this);
	  ap_out = new("ap_out", this);
	endfunction
	
	virtual function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  if (!uvm_config_db#(virtual mmg_if)::get(this,"","vif",vif))
		`uvm_fatal("MON","interface not found");
	endfunction
	
	virtual task run_phase(uvm_phase phase);
	  mmg_trans tr;
	  // wait for reset release
	  wait (!vif.rst);
	  
	  repeat(4) @(posedge vif.clk);
	  
	  forever begin
		// pull out all transactions queued by the driver
		while (fifo.try_get(tr)) begin
		  // **now** sample the DUT signal
		  tr.motion_detected = vif.motion_detected;
		  
		  //`uvm_info(get_type_name(),
			//	  $sformatf("Monitor: enable=%0d, pixel=0x%08h, last_in_frame=%0b, wr_background=%0b, threshold=%0d, motion_detected=%0b", 
				//			tr.enable, tr.pixel, tr.last_in_frame, tr.wr_background, tr.threshold, tr.motion_detected),
				 // UVM_MEDIUM);
		  
		  ap_out.write(tr);
		  @(posedge vif.clk);
		end
	  end
	endtask
  endclass


