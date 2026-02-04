//------------------------------------------------------------------------------
// File          : labler_scoreboard.sv
// Project       : Project_RTL
// Author        : eposmk
// Creation date : May 23, 2025
// Description   : UVM scoreboard for labler component
//------------------------------------------------------------------------------

class labler_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(labler_scoreboard)

  // analysis import from agent
  uvm_analysis_imp#(labler_trans, labler_scoreboard) ap;

  // error tracking
  int unsigned error_count;

  // label range
  localparam int LABEL_WIDTH = 8;
  localparam int MAX_LABELS  = 1 << LABEL_WIDTH;
  int next_label;

  // mismatch flags
  bit error_current_label;
  bit error_new_label_valid;
  bit error_new_label_value;
  bit error_merge_labels;
  bit error_merge_a;
  bit error_merge_b;

  // constructor
  function new(string name = "labler_scoreboard", uvm_component parent = null);
	super.new(name, parent);
  endfunction: new

  // build phase: initialize and create analysis imp
  virtual function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	error_count = 0;
	next_label  = 1;
	ap = new("ap", this);
  endfunction: build_phase

  // report phase
  virtual function void report_phase(uvm_phase phase);
	super.report_phase(phase);
	if (error_count > 0)
	  `uvm_info(get_full_name(), $sformatf(
		"Test failed: %0d mismatches detected", error_count), UVM_LOW)
	else
	  `uvm_info(get_full_name(), "Test passed: no mismatches", UVM_LOW)
  endfunction: report_phase

  // analysis write: compare expected vs actual
  virtual function void write(labler_trans tr);
	labler_trans expected;
	expected = new();

	// default expected fields
	expected.new_label_valid = 0;
	expected.new_label_value = 0;
	expected.current_label   = 0;
	expected.merge_labels    = 0;
	expected.merge_a         = 0;
	expected.merge_b         = 0;

	// model behavior
	if (tr.enable && tr.motion_pixel) begin
	  if (tr.left_label == 0 && tr.top_label == 0) begin
		expected.new_label_valid = 1;
		expected.new_label_value = next_label;
		expected.current_label   = next_label;
	  end else if (tr.left_label != 0 && tr.top_label == 0) begin
		expected.current_label = tr.left_label;
	  end else if (tr.left_label == 0 && tr.top_label != 0) begin
		expected.current_label = tr.top_label;
	  end else begin
		// both neighbors non-zero: pick smaller and merge
		if (tr.left_label < tr.top_label) begin
		  expected.current_label = tr.left_label;
		  expected.merge_labels  = 1;
		  expected.merge_a       = tr.left_label;
		  expected.merge_b       = tr.top_label;
		end else if (tr.top_label < tr.left_label) begin
		  expected.current_label = tr.top_label;
		  expected.merge_labels  = 1;
		  expected.merge_a       = tr.top_label;
		  expected.merge_b       = tr.left_label;
		end else begin
		  expected.current_label = tr.left_label;
		end
	  end
	  if(next_label == 0) next_label = 0;
	  else next_label = (expected.new_label_valid) ? next_label+1 : next_label;
	  if(next_label > 255)  next_label = 0;
	end
	if(tr.enable && tr.last_in_frame) next_label = 1;

	// compare
	error_current_label    = (tr.current_label   != expected.current_label);
	error_new_label_valid  = (tr.new_label_valid != expected.new_label_valid);
	error_new_label_value  = (tr.new_label_value != expected.new_label_value);
	error_merge_labels     = (tr.merge_labels    != expected.merge_labels);
	error_merge_a          = (tr.merge_a         != expected.merge_a);
	error_merge_b          = (tr.merge_b         != expected.merge_b);

	if (error_current_label || error_new_label_valid || error_new_label_value ||
			error_merge_labels || error_merge_a || error_merge_b) begin
			error_count++;
			`uvm_error(get_full_name(), $sformatf({
				"Mismatch #%0d:\n",
				"  current_label:   exp=%0d got=%0d\n",
				"  new_label_valid: exp=%0d got=%0d\n",
				"  new_label_value: exp=%0d got=%0d\n",
				"  merge_labels:    exp=%0d got=%0d\n",
				"  merge_a:         exp=%0d got=%0d\n",
				"  merge_b:         exp=%0d got=%0d\n",
				"  next_label:              got=%0d" }
				,
				error_count,
				expected.current_label,    tr.current_label,
				expected.new_label_valid, tr.new_label_valid,
				expected.new_label_value, tr.new_label_value,
				expected.merge_labels,     tr.merge_labels,
				expected.merge_a,          tr.merge_a,
				expected.merge_b,          tr.merge_b,
				next_label
			));
		end else begin
			`uvm_info(get_full_name(), $sformatf({
				"PASSED\n",
				"  current_label:   exp=%0d got=%0d\n",
				"  new_label_valid: exp=%0d got=%0d\n",
				"  new_label_value: exp=%0d got=%0d\n",
				"  merge_labels:    exp=%0d got=%0d\n",
				"  merge_a:         exp=%0d got=%0d\n",
				"  merge_b:         exp=%0d got=%0d\n",
				"  next_label:              got=%0d" }
				,
				expected.current_label,    tr.current_label,
				expected.new_label_valid, tr.new_label_valid,
				expected.new_label_value, tr.new_label_value,
				expected.merge_labels,     tr.merge_labels,
				expected.merge_a,          tr.merge_a,
				expected.merge_b,          tr.merge_b,
				next_label
			), UVM_MEDIUM);
		end
		
  endfunction: write

endclass: labler_scoreboard