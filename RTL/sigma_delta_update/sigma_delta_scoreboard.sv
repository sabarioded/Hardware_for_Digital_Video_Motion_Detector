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

  virtual function void build_phase(uvm_phase phase);
	super.build_phase(phase);
  endfunction

  virtual function void write(sigma_delta_transaction tr);
	integer diff;
	bit motion_detected_error = 0;
	bit background_next_error = 0;
	bit variance_next_error = 0;

	sigma_delta_transaction expected = new();

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

	// === MOTION DETECTION ===
	expected.motion_detected = (diff >= tr.variance);

	// === COMPARISONS ===
	if (expected.motion_detected !== tr.motion_detected)
	  motion_detected_error = 1;

	if (expected.background_next !== tr.background_next)
	  background_next_error = 1;

	if (expected.variance_next !== tr.variance_next)
	  variance_next_error = 1;

	// === RESULTS ===
	if (motion_detected_error || background_next_error || variance_next_error) begin
	  `uvm_error("SCOREBOARD", $sformatf("? Mismatch! \nInput: curr_pixel=%0d, background=%0d, variance=%0d, wr_background=%0b \nExpected: motion=%0b bg_next=%0d var_next=%0d \nGot: motion=%0b bg_next=%0d var_next=%0d",
									   tr.curr_pixel, tr.background, tr.variance, tr.wr_background,
									   expected.motion_detected, expected.background_next, expected.variance_next,
									   tr.motion_detected, tr.background_next, tr.variance_next))
	end
	else begin
	  `uvm_info("SCOREBOARD", "? Transaction passed", UVM_LOW);
	end
	//DEBUG
	`uvm_info("SCOREBOARD", ">>> Got transaction in scoreboard", UVM_MEDIUM)
  endfunction

endclass