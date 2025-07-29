/*------------------------------------------------------------------------------
 * File          : motion_detector_scoreboard.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class motion_detector_scoreboard extends uvm_scoreboard;
	`uvm_component_utils(motion_detector_scoreboard)

	uvm_analysis_imp#(motion_detector_transaction, motion_detector_scoreboard) ap;

	function new(string name = "motion_detector_scoreboard", uvm_component parent);
	  super.new(name, parent);
	  ap = new("ap", this);
	endfunction
	
	int unsigned error_count;
	virtual function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  error_count = 0;
	endfunction
	
	function void report_phase(uvm_phase phase);
		super.report_phase(phase);
		if (error_count > 0)
			`uvm_info("SCOREBOARD", $sformatf("? Test failed. Total mismatches: %0d", error_count), UVM_NONE)
		else
			`uvm_info("SCOREBOARD", "? Test passed. All transactions matched.", UVM_NONE)
	endfunction
	
	int unsigned cycle_count = 0;
	virtual function void write(motion_detector_transaction tr);
	  bit expected_motion;
	  int pixel_diff, background_diff;

	  // === Calculate expected behavior ===
	  pixel_diff = (tr.curr_pixel > tr.prev_pixel) ?
					(tr.curr_pixel - tr.prev_pixel) :
					(tr.prev_pixel - tr.curr_pixel);

	  background_diff = (tr.curr_pixel > tr.background) ?
						(tr.curr_pixel - tr.background) :
						(tr.background - tr.curr_pixel);
	  
	  cycle_count++;
	  if (cycle_count <= 2) begin
		 `uvm_info("SCOREBOARD", $sformatf("Skipping cycle %0d (initialization)", cycle_count), UVM_MEDIUM)
		 return;
	  end

	  if (tr.enable) begin
		  expected_motion = (pixel_diff > tr.threshold) && (background_diff >= tr.variance);
	  end

	  // === Compare ===
	  if (tr.enable && expected_motion !== tr.motion_detected) begin
		  error_count++;
		`uvm_error("SCOREBOARD", $sformatf(
		  "\nMismatch detected:\nInput: enable=%0b curr_pixel=%0d prev_pixel=%0d background=%0d variance=%0d threshold=%0d\nExpected: motion_detected=%0b\nGot: motion_detected=%0b",
		  tr.enable, tr.curr_pixel, tr.prev_pixel, tr.background, tr.variance, tr.threshold,
		  expected_motion, tr.motion_detected))
	  end else begin
		/*`uvm_info("SCOREBOARD", $sformatf(
		  "Transaction passed: motion_detected=%0b", tr.motion_detected), UVM_LOW)*/
	  end
	endfunction

endclass
