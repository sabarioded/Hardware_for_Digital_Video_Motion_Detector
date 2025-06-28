/*------------------------------------------------------------------------------
 * File          : mmg_scoreboard.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 17, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mmg_scoreboard extends uvm_scoreboard;
	`uvm_component_utils(mmg_scoreboard)

	// analysis port to receive transactions
	uvm_analysis_imp#(mmg_trans, mmg_scoreboard) ap_in;

	// frame dimensions (fixed)
	int                   width;
	int                   height;

	// buffer for last frames gray pixels
	bit [7:0]             fm_map[];
	bit [7:0]			background[];
	bit [7:0]			variance[];
	
	// stream position
	int                   frame_number;
	int                   pixel_count;
	int unsigned error_count; 

	function new(string name = "fm_scoreboard",
				 uvm_component parent = null);
	  super.new(name, parent);
	  ap_in = new("ap_in", this);
	  frame_number = 0;
	  pixel_count  = 0;
	endfunction

	// allocate the map using your fixed dimensions
	virtual function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  error_count = 0;

	  // use the values you set
	  width  = 32;
	  height = 24;

	  // allocate & clear buffers
	  fm_map = new[width * height];
	  foreach (fm_map[i]) fm_map[i] = 8'h00;
	  background = new[width * height];
	  foreach (background[i]) background[i] = 8'h00;
	  variance = new[width * height];
	  foreach (variance[i]) variance[i] = 8'h02;
	endfunction
	
	function void report_phase(uvm_phase phase);
		super.report_phase(phase);
		if (error_count > 0)
			`uvm_info("SCOREBOARD", $sformatf("Test failed. Total mismatches: %0d", error_count), UVM_NONE)
		else
			`uvm_info("SCOREBOARD", "Test passed. All transactions matched.", UVM_NONE)
	endfunction

	// called by ap.write( tr )
	virtual function void write(input mmg_trans tr);
	  bit [7:0] expected_gray;
	  bit [7:0] expected_prev;
	  bit [7:0] expected_bg_next;
	  bit [7:0] expected_var_next;
	  
	  bit [15:0] calc;
	  int       idx = pixel_count;
	  integer diff;
	  integer pixel_diff;
	  integer background_diff;
	  integer expected_motion;

	  // only check when DUT is driving valid data
	  if (!tr.enable) begin
		return;
	  end

	  // compute expected grayscale
	  calc = ((tr.pixel[31:24]*8'd77)
					 + (tr.pixel[23:16]*8'd150)
					 + (tr.pixel[15:8] *8'd29));
	  expected_gray = calc[15:8];

	  // determine expected prev_pixel
	  expected_prev = (frame_number == 0)
					? 8'h00
					: fm_map[idx];


	  // store this gray into buffer for next frame
	  fm_map[idx] = expected_gray;
	  
	  // === VARIANCE NEXT ===
	  diff = (expected_gray > background[idx]) ? (expected_gray - background[idx]) :
			  (background[idx] - expected_gray);

	  if (diff > variance[idx]) begin
		 variance[idx] = (variance[idx] > 253) ? 8'd255 : variance[idx] + 2;
	  end
	  else if (diff < variance[idx]) begin
		  variance[idx] = (variance[idx] < 4) ? 8'd2 : variance[idx] - 2;
	  end
	 
	  // === BACKGROUND NEXT ===
	  if (tr.wr_background) begin
		  background[idx] = expected_gray;
	  end
	  else if (expected_gray >  background[idx]) begin
		  background[idx] =  (background[idx] == 8'd255) ? 8'd255 : background[idx] + 1;
	  end
	  else if(expected_gray <  background[idx])begin
		  background[idx] = (background[idx] == 8'd0) ? 8'd0 : background[idx] - 1;
	  end	
	  
	  
	  pixel_diff = (expected_gray > expected_prev) ?
			  (expected_gray - expected_prev) :
			  (expected_prev - expected_gray);

      background_diff = (expected_gray > background[idx]) ?
				   (expected_gray - background[idx]) :
				   (background[idx] - expected_gray);


      expected_motion = (pixel_diff > tr.threshold) && (background_diff >= variance[idx]);
	  
	  if (tr.motion_detected !== expected_motion) begin
		  error_count++;
		  `uvm_error(get_full_name(),
			$sformatf("Frame %0d Pixel %0d: motion_detected wrong; exp=0x%0d got=0x%0d",
					  frame_number, idx, expected_motion, tr.motion_detected))
	  end


	  //`uvm_info("SCOREBOARD", $sformatf("Input: curr_pixel=%0d ,expected_prev=%0d ,background=%0d, variance=%0d, threshold=%0d, wr_background=%0b Expected: motion_detected=%0d Got: motion_detected=%0d",
		//	  expected_gray, expected_prev, 
			//  background[idx], variance[idx], tr.threshold, tr.wr_background,
			  //expected_motion, tr.motion_detected),UVM_LOW)

	  // advance counters
	  pixel_count++;
	  if (tr.last_in_frame) begin
		frame_number++;
		pixel_count = 0;
	  end
	endfunction

  endclass: mmg_scoreboard
