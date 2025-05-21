/*------------------------------------------------------------------------------
 * File          : fm_driver.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 15, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class fm_driver extends uvm_driver#(fm_trans);
	`uvm_component_utils(fm_driver)

	virtual fm_if vif;

	// Constructor
	function new(string name = "fm_driver", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	// Grab virtual interface
	virtual function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  if (!uvm_config_db#(virtual fm_if)::get(this, "", "vif", vif)) begin
		`uvm_fatal(get_type_name(), "Virtual interface not found")
	  end
	endfunction

	// Main driver loop
	virtual task run_phase(uvm_phase phase);
	  fm_trans tr;

	  wait (!vif.rst);
	  @(posedge vif.clk);
	  
	  //@(posedge vif.clk);

	  forever begin
		  #1ns
		seq_item_port.get_next_item(tr);

		vif.enable <= tr.enable;
		vif.pixel  <= tr.pixel;
		vif.last_in_frame   <= tr.last_in_frame;
		vif.wr_background <= tr.wr_background;

		@(posedge vif.clk);

		seq_item_port.item_done();
	  end

	endtask

  endclass
