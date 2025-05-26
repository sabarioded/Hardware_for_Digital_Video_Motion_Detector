/*------------------------------------------------------------------------------
 * File          : lm_scoreboard.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 26, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class lm_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(lm_scoreboard)

  // analysis import from agent
  uvm_analysis_imp#(lm_trans, lm_scoreboard) ap;

  // error tracking
  int unsigned error_count;
  int expected;
  int root1;
  int root2;

  // label range
  localparam int LABEL_WIDTH = 8;
  localparam int NUM_LABELS  = 1 << LABEL_WIDTH;
  int label_table[NUM_LABELS];

  // constructor
  function new(string name = "lm_scoreboard", uvm_component parent = null);
	super.new(name, parent);
  endfunction: new

  // build phase: initialize and create analysis imp
  virtual function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	error_count = 0;
	root1 = 0;
	root2 = 0;
	for (int i = 0; i < NUM_LABELS; i++)
		label_table[i] = i;  // self-parented
	
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
  virtual function void write(lm_trans tr);

	// model behavior
	if(tr.enable && tr.resolve_valid) begin
		root1 = label_table[tr.resolve_label];
		root2 = label_table[root1];
		expected = (root2 == root1) ? root1 : root2;
	end else begin
		expected = 0;
	end
	if(tr.enable && tr.merge_valid) begin
		label_table[tr.merge_b] = tr.merge_a;
	end
	

	// compare
	if (expected != tr.resolved_label) begin
			error_count++;
			`uvm_error(get_full_name(), $sformatf({
				"Mismatch #%0d:\n",
				"  resolved_label:   exp=%0d got=%0d\n"}
				,
				error_count,
				expected    ,    tr.resolved_label
			));
		end else begin
			`uvm_info(get_full_name(), $sformatf({
				"PASSED\n",
				"  resolved_label:   exp=%0d got=%0d\n" }
				,
				expected,    tr.resolved_label
			), UVM_MEDIUM);
		end
		
  endfunction: write

endclass: lm_scoreboard