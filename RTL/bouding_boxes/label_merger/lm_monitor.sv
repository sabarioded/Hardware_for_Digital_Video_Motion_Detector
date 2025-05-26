/*------------------------------------------------------------------------------
 * File          : lm_monitor.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 26, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class lm_monitor extends uvm_monitor #(lm_trans);
	`uvm_component_utils(lm_monitor)
	
	virtual lm_if vif;
	
	uvm_tlm_analysis_fifo #(lm_trans) fifo;
	uvm_analysis_port #(lm_trans) ap;
	
	function new(string name = "lm_monitor", uvm_component parent = null);
		super.new(name,parent);
		fifo = new("fifo",this);
		ap = new("ap",this);
	endfunction
	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db#(virtual lm_if)::get(this,"","vif",vif))
		  `uvm_fatal("MONITOR","interface not found");
	endfunction
	
	virtual task run_phase(uvm_phase phase);
		lm_trans tr;
		wait(!vif.rst);
		
		repeat(3) @(posedge vif.clk);
		
		forever begin
			while(fifo.try_get(tr)) begin
				`uvm_info(get_type_name(),
					  $sformatf("Monitor: enable=%0d, merge_valid=0x%0d, merge_a=%0d, merge_b=%0d, resolve_valid=%0d, resolve_label=%0d,", 
								tr.enable, tr.merge_valid, tr.merge_a, tr.merge_b, tr.resolve_valid, tr.resolve_label),
					  UVM_MEDIUM);
				
				tr.resolved_label = vif.resolved_label;
				
				ap.write(tr);
				@(posedge vif.clk);
			end
		end
	endtask
	
endclass