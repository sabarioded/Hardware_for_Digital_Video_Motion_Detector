/*------------------------------------------------------------------------------
 * File          : lm_scoreboard.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 26, 2025
 * Description   : Scoreboard for label_merger with MAX_PATH_DEPTH support
 *------------------------------------------------------------------------------*/

class lm_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(lm_scoreboard)

  // Analysis import from agent
  uvm_analysis_imp#(lm_trans, lm_scoreboard) ap;

  // Error tracking
  int unsigned error_count;
  int expected;

  // Model table
  localparam int LABEL_WIDTH     = 8;
  localparam int NUM_LABELS      = 1 << LABEL_WIDTH;
  localparam int MAX_PATH_DEPTH  = 4;
  int label_table[NUM_LABELS];

  // Constructor
  function new(string name = "lm_scoreboard", uvm_component parent = null);
	super.new(name, parent);
  endfunction

  // Build phase: init model and imp
  virtual function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	error_count = 0;
	// Initialize as identity
	for (int i = 0; i < NUM_LABELS; i++)
	  label_table[i] = i;
	ap = new("ap", this);
  endfunction

  // Report phase summary
  virtual function void report_phase(uvm_phase phase);
	super.report_phase(phase);
	if (error_count > 0)
	  `uvm_info(get_full_name(), $sformatf("Test failed: %0d mismatches detected", error_count), UVM_LOW)
	else
	  `uvm_info(get_full_name(), "Test passed: no mismatches", UVM_LOW)
  endfunction

  // Analysis write: update model and compare
  virtual function void write(lm_trans tr);
	// 3) Compute expected resolved_label
	if (tr.enable && tr.resolve_valid) begin
	  int r = label_table[tr.resolve_label];
	  for (int d = 1; d < MAX_PATH_DEPTH; d++)
		r = label_table[r];
	  expected = r;
	end else begin
	  expected = 0;
	end

	// 4) Compare
	if (expected != tr.resolved_label) begin
	  error_count++;
	  `uvm_error(get_full_name(), $sformatf(
		"Mismatch #%0d:\n  expected=%0d got=%0d",
		error_count, expected, tr.resolved_label
	  ));
	end else begin
	  `uvm_info(get_full_name(), $sformatf(
		"PASSED: resolved_label=%0d",
		expected
	  ), UVM_MEDIUM);
	end

	// 1) Handle reset of table on new frame
	if (tr.enable && tr.last_in_frame) begin
	  for (int i = 0; i < NUM_LABELS; i++)
		label_table[i] = i;
	end
	// 2) Handle merge
	if (tr.enable && tr.merge_valid) begin
	  // Compute root of merge_a over MAX_PATH_DEPTH
	  int a_root = label_table[tr.merge_a];
	  for (int d = 1; d < MAX_PATH_DEPTH; d++)
		a_root = label_table[a_root];
	  // Apply union
	  label_table[tr.merge_b] = a_root;
	end
	
  endfunction

endclass: lm_scoreboard
