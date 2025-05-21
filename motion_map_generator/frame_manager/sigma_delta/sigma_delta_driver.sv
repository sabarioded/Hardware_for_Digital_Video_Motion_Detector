/*------------------------------------------------------------------------------
 * File          : sigma_delta_driver.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 5, 2025
 * Description   :
 *------------------------------------------------------------------------------*/
class sigma_delta_driver extends uvm_driver #(sigma_delta_transaction);
	`uvm_component_utils(sigma_delta_driver)

	virtual sigma_delta_if vif;

	function new(string name = "sigma_delta_driver", uvm_component parent);
		super.new(name, parent);
	endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db#(virtual sigma_delta_if)::get(this, "", "vif", vif)) begin
		  `uvm_fatal("DRIVER", "Failed to get vif from config DB");
		end
	  endfunction


	task run_phase(uvm_phase phase);
		sigma_delta_transaction tr;
		vif.rst = 1;
		vif.enable = 0;
		@(posedge vif.clk);
		vif.rst = 0;
		@(posedge vif.clk);

		
		forever begin
			
			#1ns
			seq_item_port.get_next_item(tr);
			vif.enable        <= tr.enable;
			vif.wr_background <= tr.wr_background;
			vif.curr_pixel    <= tr.curr_pixel;
			vif.background    <= tr.background;
			vif.variance      <= tr.variance;
			@(posedge vif.clk); 

			seq_item_port.item_done();
		end
	endtask

endclass

