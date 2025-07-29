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
		  if(expected_list[i].frame_id > tr.frame_id+3) begin
			  expected_list.delete(i);
		  end
	  end
	end

	if (tr.pixel_valid) begin
		if(tr.enable == 0) begin
			`uvm_error("SCOREBOARD"," enable low and valid high");
		end
	  on_any_edge = 0;
	  // Determine if current pixel is on the delayed box outline
	  foreach (expected_list[i]) begin
		// Left/right edge
		if ((tr.x == expected_list[i].min_x || tr.x == expected_list[i].max_x) &&
			(expected_list[i].min_y <= tr.y && tr.y <= expected_list[i].max_y) && expected_list[i].frame_id == tr.frame_id) begin
		  on_any_edge = 1; break;
		end
		// Top/bottom edge
		if ((tr.y == expected_list[i].min_y || tr.y == expected_list[i].max_y) &&
			(expected_list[i].min_x <= tr.x && tr.x <= expected_list[i].max_x) && expected_list[i].frame_id == tr.frame_id) begin
		  on_any_edge = 1; break;
		end
	  end

	  expected_pixel = on_any_edge ? HIGHLIGHT_COLOR : tr.rbg_pixel;

	  // Pixel comparison
	  if (tr.highlighted_pixel !== expected_pixel) begin
		`uvm_error("SCOREBOARD",
		  $sformatf("Pixel mismatch @ (x=%0d, y=%0d): DUT drove 0x%08h, expected 0x%08h, frame = %0d",
					tr.x, tr.y, tr.highlighted_pixel, expected_pixel, tr.frame_id)
		);
		error_count++;
	  end else begin
		/*`uvm_info("SCOREBOARD",
		  $sformatf("Pixel MATCH @ (x=%0d, y=%0d): DUT drove 0x%08h, expected 0x%08h, frame = %0d",
					tr.x, tr.y, tr.highlighted_pixel, expected_pixel, tr.frame_id), UVM_MEDIUM);*/
	  end 
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