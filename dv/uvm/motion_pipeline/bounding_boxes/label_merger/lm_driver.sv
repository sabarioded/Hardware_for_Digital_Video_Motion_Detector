/*------------------------------------------------------------------------------
 * File          : lm_driver.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 26, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class lm_driver extends uvm_driver #(lm_trans);
	`uvm_component_utils(lm_driver)
	
	virtual lm_if vif;
	
	uvm_analysis_port#(lm_trans) ap;
	
	function new(string name = "lm_driver", uvm_component parent = null);
		super.new(name,parent);
		ap = new("ap",this);
	endfunction
	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db#(virtual lm_if)::get(this, "", "vif", vif)) begin
			`uvm_fatal(get_type_name(), "Virtual interface not found")
		  end
	endfunction
	
	virtual task run_phase(uvm_phase phase);
		lm_trans tr;
		wait(!vif.rst);
		
		repeat(2) @(posedge vif.clk);
		
		forever begin
			#1ns
			seq_item_port.get_next_item(tr);
			vif.enable = tr.enable;
			vif.last_in_frame = tr.last_in_frame;
			vif.merge_valid = tr.merge_valid;
			vif.merge_a = tr.merge_a;
			vif.merge_b = tr.merge_b;
			vif.resolve_valid = tr.resolve_valid;
			vif.resolve_label = tr.resolve_label;
			
			ap.write(tr);
			seq_item_port.item_done();
			@(posedge vif.clk);
					
		end
	endtask
endclass