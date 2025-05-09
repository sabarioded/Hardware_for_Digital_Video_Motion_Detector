/*------------------------------------------------------------------------------
 * File          : box_filter_driver.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class box_filter_driver extends uvm_driver #(box_filter_transaction);
	`uvm_component_utils(box_filter_driver)

	virtual box_filter_if vif;

	function new(string name = "box_filter_driver", uvm_component parent);
		super.new(name, parent);
	endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db#(virtual box_filter_if)::get(this, "", "vif", vif)) begin
			`uvm_fatal("DRIVER", "Failed to get vif from config DB");
		end
	endfunction

	task run_phase(uvm_phase phase);
		box_filter_transaction tr;

		vif.rst = 1;
		@(posedge vif.clk);
		vif.rst = 0;
		// Initialize outputs
		vif.enable          = 0;
		vif.neighbors_number = 0;
		vif.motion_map      = 0;
		@(posedge vif.clk);

		@(posedge vif.clk); // wait one clock after reset

		forever begin
			seq_item_port.get_next_item(tr);

			// Apply inputs 1ns after clock to match monitor & DUT timing
			@(posedge vif.clk);
			#1ns;

			vif.enable          = tr.enable;
			vif.neighbors_number = tr.neighbors_number;
			vif.motion_map      = tr.motion_map;

			seq_item_port.item_done();
		end
	endtask

endclass
