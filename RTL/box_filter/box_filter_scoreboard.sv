/*------------------------------------------------------------------------------
 * File          : box_filter_scoreboard.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class box_filter_scoreboard extends uvm_scoreboard;
	`uvm_component_utils(box_filter_scoreboard)

	uvm_analysis_imp#(box_filter_transaction, box_filter_scoreboard) ap;

	function new(string name = "box_filter_scoreboard", uvm_component parent);
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
			`uvm_info("SCOREBOARD", "Test passed. All transactions matched.", UVM_NONE)
	endfunction
	
	logic expected_filtered_motion;
	int unsigned motion_pixel_count;
	int unsigned cycle_count = 0;
	virtual function void write(box_filter_transaction tr);
		cycle_count++;

		if (cycle_count <= 2) begin
			`uvm_info("SCOREBOARD", $sformatf("Skipping cycle %0d (initialization)", cycle_count), UVM_MEDIUM)
			return;
		end

		// === Compute expected result ===
		motion_pixel_count = 0;
		foreach (tr.motion_map[i]) begin
			motion_pixel_count += tr.motion_map[i];
		end

		expected_filtered_motion = (tr.enable) ? (motion_pixel_count > tr.neighbors_number) : 1'b0;

		// === Compare with actual ===
		if (expected_filtered_motion !== tr.filtered_motion) begin
			error_count++;
			`uvm_error("SCOREBOARD", $sformatf(
				"Mismatch detected:\n  Input: motion_map=%b, neighbors_number=%0d, enable=%0b\n  Expected: %0b, Got: %0b",
				tr.motion_map, tr.neighbors_number, tr.enable,
				expected_filtered_motion, tr.filtered_motion
			))
		end else begin
			`uvm_info("SCOREBOARD", $sformatf("Transaction passed: filtered_motion = %0b", tr.filtered_motion), UVM_MEDIUM)
		end
	endfunction


endclass
