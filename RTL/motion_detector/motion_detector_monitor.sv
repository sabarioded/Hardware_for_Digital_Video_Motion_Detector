/*------------------------------------------------------------------------------
 * File          : motion_detector_monitor.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class motion_detector_monitor extends uvm_monitor;
	`uvm_component_utils(motion_detector_monitor)

	virtual motion_detector_if vif;

	uvm_analysis_port #(motion_detector_transaction) ap;

	function new(string name = "motion_detector_monitor", uvm_component parent);
	  super.new(name, parent);
	  ap = new("ap", this);
	endfunction

	function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  // Get handle to the interface
	  if (!uvm_config_db#(virtual motion_detector_if)::get(this, "", "vif", vif)) begin
		`uvm_fatal("CONFIG_DB", "Failed to get vif from config_db");
	  end
	endfunction

	task run_phase(uvm_phase phase);
	  motion_detector_transaction tr;

	  forever begin
		@(posedge vif.clk);
		if(!vif.rst) begin
		  tr = motion_detector_transaction::type_id::create("tr", this);
		  tr.enable            = vif.enable;
		  tr.background     = vif.background;
		  tr.variance        = vif.variance;
		  tr.curr_pixel        = vif.curr_pixel;
		  tr.prev_pixel          = vif.prev_pixel;
		  tr.threshold          = vif.threshold;
		  #1ns
		  tr.motion_detected  = vif.motion_detected;		  
		  ap.write(tr);

		end
		end
	endtask

  endclass
