/*------------------------------------------------------------------------------
 * File          : mp_driver.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jun 11, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mp_driver extends uvm_driver #(mp_trans);
	// factory
	`uvm_component_utils(mp_driver)
	
	//interface
	virtual mp_if vif;
	
	//analysis port
	uvm_analysis_port#(mp_trans) ap;
	
	// 2-cycle delay buffer
	logic [31:0] memory_pixel_pipe[$];
	
	//constructor
	function new(name = "mp_driver", uvm_component parent=null);
		super.new(name,parent);
		ap = new("ap",this);
	endfunction
	
	// grab the virtual interface in build phase
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db#(virtual mp_if)::get(this, "", "vif", vif)) begin
			`uvm_fatal(get_type_name(), "Virtual interface not found")
		  end
	endfunction
	
	// drive the signals in run phase
	virtual task run_phase(uvm_phase phase);
		mp_trans tr;
		wait(!vif.rst);
		
		repeat(2) @(posedge vif.clk);
		
		forever begin
			#1ns
			seq_item_port.get_next_item(tr);
			
			memory_pixel_pipe.push_back(tr.memory_pixel);
			if (memory_pixel_pipe.size() > 2)
			  memory_pixel_pipe.pop_front();
			
			vif.enable = tr.enable;
			vif.wr_background = tr.wr_background;
			vif.rbg_pixel = tr.rbg_pixel;
			vif.last_in_frame = tr.last_in_frame;
			vif.threshold = tr.threshold;
			vif.width = tr.width;
			vif.height = tr.height;
			
			if (memory_pixel_pipe.size() >= 2)
				vif.memory_pixel = memory_pixel_pipe[0];
			  else
				vif.memory_pixel = 32'h00000000;
			
			ap.write(tr);
			
			seq_item_port.item_done();
			
			@(posedge vif.clk);
		end
	endtask
endclass
