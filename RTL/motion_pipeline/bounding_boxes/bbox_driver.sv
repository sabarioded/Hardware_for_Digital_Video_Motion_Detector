/*------------------------------------------------------------------------------
 * File          : bbox_driver.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 27, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class bbox_driver extends uvm_driver #(bbox_trans);
	// factory
	`uvm_component_utils(bbox_driver)
	
	//interface
	virtual bbox_if vif;
	
	//analysis port
	uvm_analysis_port#(bbox_trans) ap;
	
	//constructor
	function new(name = "bbox_driver", uvm_component parent=null);
		super.new(name,parent);
		ap = new("ap",this);
	endfunction
	
	// grab the virtual interface in build phase
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db#(virtual bbox_if)::get(this, "", "vif", vif)) begin
			`uvm_fatal(get_type_name(), "Virtual interface not found")
		  end
	endfunction
	
	// drive the signals in run phase
	virtual task run_phase(uvm_phase phase);
		bbox_trans tr;
		wait(!vif.rst);
		
		repeat(2) @(posedge vif.clk);
		
		forever begin
			#1ns
			seq_item_port.get_next_item(tr);
			
			vif.enable = tr.enable;
			vif.motion_pixel = tr.motion_pixel;
			vif.rbg_pixel = tr.rbg_pixel;
			vif.last_in_frame = tr.last_in_frame;
			vif.width = tr.width;
			vif.height = tr.height;
			
			ap.write(tr);
			
			seq_item_port.item_done();
			
			@(posedge vif.clk);
		end
	endtask
endclass