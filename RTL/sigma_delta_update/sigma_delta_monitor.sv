/*------------------------------------------------------------------------------
 * File         : sigma_delta_monitor.sv
 * Project      : RTL
 * Author       : eposmk
 * Creation date: May 5, 2025
 * Description  :
 *------------------------------------------------------------------------------*/

class sigma_delta_monitor extends uvm_monitor;
  `uvm_component_utils(sigma_delta_monitor)

  virtual sigma_delta_if vif;

  uvm_analysis_port #(sigma_delta_transaction) ap;

  function new(string name = "sigma_delta_monitor", uvm_component parent);
	super.new(name, parent);
	ap = new("ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	// Get handle to the interface
	if (!uvm_config_db#(virtual sigma_delta_if)::get(this, "", "vif", vif)) begin
	  `uvm_fatal("CONFIG_DB", "Failed to get vif from config_db");
	end
  endfunction

  task run_phase(uvm_phase phase);
	sigma_delta_transaction tr;

	forever begin
	  @(posedge vif.clk);
	  if(!vif.rst) begin
		tr = sigma_delta_transaction::type_id::create("tr", this);
		tr.enable            = vif.enable;
		tr.wr_background     = vif.wr_background;
		tr.curr_pixel        = vif.curr_pixel;
		tr.background        = vif.background;
		tr.variance          = vif.variance;
		#1ns
		tr.background_next  = vif.background_next;
		tr.variance_next      = vif.variance_next;
		tr.motion_detected   = vif.motion_detected;
		ap.write(tr);
//		`uvm_info("MONITOR", $sformatf("Sent transaction: enable=%b, wr_background=%b, curr_pixel=%d, background=%d, variance=%d, background_next=%d, variance_next=%d, motion_detected=%b",
//									 tr.enable, tr.wr_background, tr.curr_pixel, tr.background, tr.variance, tr.background_next, tr.variance_next, tr.motion_detected), UVM_HIGH);
	  end
	  end
  endtask

endclass
