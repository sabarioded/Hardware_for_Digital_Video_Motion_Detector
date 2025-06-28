/*------------------------------------------------------------------------------
 * File          : bbox_scoreboard.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 27, 2025
 * Description   : Scoreboard verifying DUT boxes against expected boxes,
 *                 ignoring labels, with one-frame delay
 *------------------------------------------------------------------------------*/

// Declare specialized analysis implementation types
`uvm_analysis_imp_decl(_exp)
`uvm_analysis_imp_decl(_dut)

class bbox_scoreboard extends uvm_component;
  `uvm_component_utils(bbox_scoreboard)

  // analysis imports
  uvm_analysis_imp_exp #(bbox_trans, bbox_scoreboard) expected_imp;
  uvm_analysis_imp_dut #(bbox_trans, bbox_scoreboard) dut_imp;

  // box type and queues
  typedef struct packed {
	int frame_id;
	int unsigned min_x, min_y;
	int unsigned max_x, max_y;
	int unsigned label;
  } box_t;

  box_t expected_list[$]; // boxes captured by write_exp() for frame N

  int unsigned error_count;
  logic [31:0] expected_pixel;
  localparam HIGHLIGHT_COLOR = 32'hFF000000;
  bit on_any_edge;

  function new(string name, uvm_component parent = null);
	super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	expected_imp = new("expected_imp", this);
	dut_imp      = new("dut_imp", this);
	error_count  = 0;
  endfunction
	
  box_t bb;
  int idx;
  bit found;
  // Capture expected boxes as they arrive
  virtual function void write_exp(bbox_trans tr);
	box_t b;
	b.frame_id = tr.frame_id;
	b.label = tr.bbox_label;
	b.min_x = tr.bbox_min_x;
	b.min_y = tr.bbox_min_y;
	b.max_x = tr.bbox_max_x;
	b.max_y = tr.bbox_max_y;
	expected_list.push_back(b);
	`uvm_info("SCOREBOARD", $sformatf(
	  "Added expected box: (%0d,%0d)-(%0d,%0d) in frame %0d",
	  b.min_x, b.min_y, b.max_x, b.max_y, b.frame_id), UVM_MEDIUM)
  endfunction

  // Compare DUT output, applying a one-frame delay
  virtual function void write_dut(bbox_trans tr);
	if (tr.last_in_frame) begin
	  foreach (expected_list[i]) begin
		  if(expected_list[i].frame_id > tr.frame_id+2) begin
			  expected_list.delete(i);
		  end
	  end
	end	
	
	found = 0;
	
	if (tr.bbox_valid) begin  // only consider valid boxes
	  // search for matching coordinates
	  for (idx = 0; idx < expected_list.size(); idx++) begin
		bb = expected_list[idx];
		if (tr.bbox_min_x == bb.min_x &&
			tr.bbox_min_y == bb.min_y &&
			tr.bbox_max_x == bb.max_x &&
			tr.bbox_max_y == bb.max_y) begin
		  found = 1;
		  break;
		end
	  end
	  
	  if (found) begin
		expected_list.delete(idx);
		`uvm_info("SCOREBOARD", $sformatf("Matched DUT box: (%0d,%0d)-(%0d,%0d) frame_id=%0d",
										  tr.bbox_min_x, tr.bbox_min_y, 
										  tr.bbox_max_x, tr.bbox_max_y, tr.frame_id), UVM_MEDIUM)
	  end else begin
		`uvm_error("SCOREBOARD", $sformatf(
		  "Unexpected DUT box: (%0d,%0d)-(%0d,%0d) - frame_id=%0d",
		  tr.bbox_min_x, tr.bbox_min_y, tr.bbox_max_x, tr.bbox_max_y, tr.frame_id
		));
		error_count++;
	  end
	end else begin
	  `uvm_info("SCOREBOARD", "Received invalid DUT box (bbox_valid is false), skipping.", UVM_HIGH)
	end

	 
  endfunction

  // Report results at end of simulation
  virtual function void report_phase(uvm_phase phase);
	super.report_phase(phase);

	if (error_count == 0) begin
	  `uvm_info("SCOREBOARD", "All frames verified successfully: no pixel mismatches!", UVM_LOW)
	end else begin
	  `uvm_info("SCOREBOARD",
		$sformatf("SCOREBOARD SUMMARY: %0d total mismatches/errors detected.", error_count),
		UVM_LOW
	  );
	end
  endfunction

endclass: bbox_scoreboard