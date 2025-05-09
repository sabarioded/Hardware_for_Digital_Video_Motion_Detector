/*------------------------------------------------------------------------------
 * File         : sigma_delta_scoreboard.sv
 * Project      : RTL
 * Description  : Scoreboard for sigma_delta_update module
 *------------------------------------------------------------------------------*/

class sigma_delta_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(sigma_delta_scoreboard)

  uvm_analysis_imp #(sigma_delta_transaction, sigma_delta_scoreboard) ap;

  function new(string name = "sigma_delta_scoreboard", uvm_component parent);
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
  integer diff;
  bit motion_detected_error;
  bit background_next_error;
  bit variance_next_error;
  sigma_delta_transaction expected;
  virtual function void write(sigma_delta_transaction tr);
	 cycle_count++;

	 if (cycle_count <= 2) begin
		`uvm_info("SCOREBOARD", $sformatf("Skipping cycle %0d (initialization)", cycle_count), UVM_MEDIUM)
		return;
	 end

	motion_detected_error = 0;
	background_next_error = 0;
	variance_next_error = 0;

	expected = new();

	// === BACKGROUND NEXT ===
	if (tr.wr_background) begin
	  expected.background_next = tr.curr_pixel;
	end
	else if (tr.curr_pixel == tr.background) begin
	  expected.background_next = tr.background;
	end
	else if (tr.curr_pixel > tr.background) begin
	  expected.background_next = (tr.background == 8'd255) ? 8'd255 : tr.background + 1;
	end
	else begin
	  expected.background_next = (tr.background == 8'd0) ? 8'd0 : tr.background - 1;
	end

	// === VARIANCE NEXT ===
	diff = (tr.curr_pixel > tr.background) ? (tr.curr_pixel - tr.background) :
			(tr.background - tr.curr_pixel);


	if (diff > tr.variance) begin
	  expected.variance_next = (tr.variance > 253) ? 8'd255 : tr.variance + 2;
	end
	else if (diff < tr.variance) begin
	  expected.variance_next = (tr.variance < 4) ? 8'd2 : tr.variance - 2;
	end
	else begin
	  expected.variance_next = tr.variance;
	end
	
	if(!tr.enable) begin
		expected.motion_detected = 0;
		expected.variance_next = 2;
		expected.background_next = 0; 
	end

	// === MOTION DETECTION ===
	expected.motion_detected = (diff >= tr.variance); //

	// === COMPARISONS ===
	if (expected.motion_detected !== tr.motion_detected)
	  motion_detected_error = 1;

	if (expected.background_next !== tr.background_next)
	  background_next_error = 1;

	if (expected.variance_next !== tr.variance_next)
	  variance_next_error = 1;

	// === RESULTS ===
	if (motion_detected_error || background_next_error || variance_next_error) begin
		error_count++;
	  `uvm_error("SCOREBOARD", $sformatf("Mismatch! \nInput: enable = %0d, curr_pixel=%0d, background=%0d, variance=%0d, wr_background=%0b \nExpected: motion=%0b bg_next=%0d var_next=%0d \nGot: motion=%0b bg_next=%0d var_next=%0d",
									   tr.enable, tr.curr_pixel, tr.background, tr.variance, tr.wr_background,
									   expected.motion_detected, expected.background_next, expected.variance_next,
									   tr.motion_detected, tr.background_next, tr.variance_next))
	end
	else begin
	  `uvm_info("SCOREBOARD", $sformatf("Passed! \nInput: curr_pixel=%0d, background=%0d, variance=%0d, wr_background=%0b \nExpected: motion=%0b bg_next=%0d var_next=%0d \nGot: motion=%0b bg_next=%0d var_next=%0d",
			  tr.curr_pixel, tr.background, tr.variance, tr.wr_background,
			  expected.motion_detected, expected.background_next, expected.variance_next,
			  tr.motion_detected, tr.background_next, tr.variance_next),UVM_LOW)
	end
	
  endfunction

endclass