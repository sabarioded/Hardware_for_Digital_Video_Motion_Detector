/*------------------------------------------------------------------------------
 * File          : fm_monitor.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 15, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class fm_monitor extends uvm_monitor;
	`uvm_component_utils(fm_monitor)

	virtual fm_if                vif;
	uvm_analysis_port#(fm_trans) ap;

	function new(string name="fm_monitor", uvm_component parent=null);
	  super.new(name, parent);
	  ap = new("ap", this);
	endfunction

	virtual function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  if (!uvm_config_db#(virtual fm_if)::get(this, "", "vif", vif)) begin
		`uvm_fatal("MON", "fm_if not found")
	  end
	endfunction

	virtual task run_phase(uvm_phase phase);
	  fm_trans tr;
	  wait (!vif.rst);
	  repeat(2) @(posedge vif.clk);

	  forever begin
		  tr = fm_trans::type_id::create(
				{get_name(), $sformatf("_%0t", $time)});
		  tr.enable         = vif.enable;
		  tr.pixel          = vif.pixel;
		  tr.last_in_frame  = vif.last_in_frame;
		  tr.wr_background  = vif.wr_background;
		  @(posedge vif.clk);
		  tr.curr_pixel     = vif.curr_pixel;
		  tr.prev_pixel     = vif.prev_pixel;
		  tr.background_next     = vif.background_next;
		  tr.variance_next     = vif.variance_next;
		  ap.write(tr);
	  end
	endtask
  endclass
