/*------------------------------------------------------------------------------
 * File          : box_filter_monitor.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class box_filter_monitor extends uvm_monitor;
	`uvm_component_utils(box_filter_monitor)

	virtual box_filter_if vif;

	uvm_analysis_port #(box_filter_transaction) ap;

	function new(string name = "box_filter_monitor", uvm_component parent);
		super.new(name, parent);
		ap = new("ap", this);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db#(virtual box_filter_if)::get(this, "", "vif", vif)) begin
			`uvm_fatal("CONFIG_DB", "Failed to get vif from config_db");
		end
	endfunction

	task run_phase(uvm_phase phase);
		box_filter_transaction tr;

		forever begin
			@(posedge vif.clk);
			if (!vif.rst) begin
				tr = box_filter_transaction::type_id::create("tr", this);
				tr.enable           = vif.enable;
				tr.neighbors_number = vif.neighbors_number;
				tr.motion_map       = vif.motion_map;

				// Allow signals to settle
				#1ns;

				tr.filtered_motion  = vif.filtered_motion;

				ap.write(tr);

			end
		end
	endtask

endclass

