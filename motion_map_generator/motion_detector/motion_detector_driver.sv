/*------------------------------------------------------------------------------
 * File          : motion_detector_driver.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class motion_detector_driver extends uvm_driver #(motion_detector_transaction);
	`uvm_component_utils(motion_detector_driver)

	virtual motion_detector_if vif;

	function new(string name = "motion_detector_driver", uvm_component parent);
		super.new(name, parent);
	endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db#(virtual motion_detector_if)::get(this, "", "vif", vif)) begin
		  `uvm_fatal("DRIVER", "Failed to get vif from config DB");
		end
	  endfunction


	task run_phase(uvm_phase phase);
		motion_detector_transaction tr;
		vif.rst = 1;
		@(posedge vif.clk);
		vif.rst = 0;
		@(posedge vif.clk);
		
		forever begin
			
			#1ns
			seq_item_port.get_next_item(tr);
			vif.enable        <= tr.enable;
			vif.background <= tr.background;
			vif.variance    <= tr.variance;
			vif.curr_pixel    <= tr.curr_pixel;
			vif.prev_pixel      <= tr.prev_pixel;
			vif.threshold      <= tr.threshold;
			@(posedge vif.clk); 

			seq_item_port.item_done();
		end
	endtask

endclass