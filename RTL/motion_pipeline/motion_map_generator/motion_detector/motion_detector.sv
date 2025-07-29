/*------------------------------------------------------------------------------
 * File         : motion_detector.sv
 * Project      : RTL
 * Author       : eposmk
 * Creation date: May 9, 2025
 * Description  : Motion detector with inline assertions style
 *------------------------------------------------------------------------------*/

module motion_detector (
  input  logic         clk,
  input  logic         rst,
  input  logic         enable,
  input  logic [7:0]   background,
  input  logic [7:0]   variance,
  input  logic [7:0]   curr_pixel,
  input  logic [7:0]   prev_pixel,
  input  logic [7:0]   threshold,
  output logic         motion_detected
);

  // Internal signals for absolute differences
  logic [7:0] pixel_diff;
  logic [7:0] background_diff;

  assign pixel_diff      = (curr_pixel > prev_pixel) ? curr_pixel - prev_pixel : prev_pixel - curr_pixel;
  assign background_diff = (curr_pixel > background)   ? curr_pixel - background  : background  - curr_pixel;

  always_ff @(posedge clk or posedge rst) begin
	if (rst) begin
	  motion_detected <= 1'b0;
	end else if(enable) begin
	  motion_detected <= (pixel_diff > threshold) && (background_diff >= variance);
	end
  end

  `ifndef SYNTHESIS
  `ifdef ENABLE_MD_ASSERTIONS

	// --------------------------------------------------
	// [1] After reset, motion_detected must be LOW
	// --------------------------------------------------
	always @(posedge clk) begin
	  if (rst) begin
		#1;
		assert (!motion_detected)
		  else `uvm_fatal("MD_A1",
			$sformatf("[%0t] MD_A1: motion_detected=%0d not low after reset",
					  $time, motion_detected));
	  end
	end

	// --------------------------------------------------
	// [2] When DISABLED, motion_detected must always be LOW
	// --------------------------------------------------
	always @(posedge clk) begin
	  if (!rst && !enable) begin
		#1;
		assert (motion_detected == $past(motion_detected))
		  else `uvm_fatal("MD_A2",
			$sformatf("[%0t] MD_A2: motion_detected=%0d asserted while enable=0",
					  $time, motion_detected));
	  end
	end

	// --------------------------------------------------
	// [3] When ENABLED, motion_detected must assert exactly when both conditions are met
	// pixel_diff > threshold AND background_diff >= variance
	// --------------------------------------------------
	always @(posedge clk) begin
	  if (!rst && enable && (pixel_diff > threshold) && (background_diff >= variance)) begin
		#1;
		assert (motion_detected)
		  else `uvm_fatal("MD_A3",
			$sformatf("[%0t] MD_A3: motion_detected=%0d not asserted for pixel_diff=%0d > thr=%0d, bg_diff=%0d >= var=%0d",
					  $time, motion_detected, pixel_diff, threshold, background_diff, variance));
	  end
	end

	// --------------------------------------------------
	// [4] When ENABLED, if either condition is FALSE, motion_detected must be LOW
	// --------------------------------------------------
	always @(posedge clk) begin
	  if (!rst && enable && ((pixel_diff <= threshold) || (background_diff < variance))) begin
		#1;
		assert (!motion_detected)
		  else `uvm_fatal("MD_A4",
			$sformatf("[%0t] MD_A4: motion_detected=%0d incorrectly asserted for pixel_diff=%0d thr=%0d, bg_diff=%0d var=%0d",
					  $time, motion_detected, pixel_diff, threshold, background_diff, variance));
	  end
	end

	// --------------------------------------------------
	// [5] Threshold EDGE behavior: equal threshold should NOT trigger
	// --------------------------------------------------
	always @(posedge clk) begin
	  if (!rst && enable && (pixel_diff == threshold) && (background_diff >= variance)) begin
		#1;
		assert (!motion_detected)
		  else `uvm_fatal("MD_A5",
			$sformatf("[%0t] MD_A5: motion_detected asserted at equality pixel_diff==threshold=%0d", $time, threshold));
	  end
	end

	// --------------------------------------------------
	// [6] Variance EDGE behavior: exactly equal variance should trigger
	// (only if pixel_diff > threshold)
	// --------------------------------------------------
	always @(posedge clk) begin
	  if (!rst && enable && (pixel_diff > threshold) && (background_diff == variance)) begin
		#1;
		assert (motion_detected)
		  else `uvm_fatal("MD_A6",
			$sformatf("[%0t] MD_A6: motion_detected not asserted when bg_diff==variance=%0d", $time, variance));
	  end
	end

	// --------------------------------------------------
	// [7] Illegal inputs sanity check
	// threshold==0 means ANY diff >0 should trigger
	// --------------------------------------------------
	always @(posedge clk) begin
	  if (!rst && enable && (threshold == 0) && (pixel_diff > 0) && (background_diff >= variance)) begin
		#1;
		assert (motion_detected)
		  else `uvm_fatal("MD_A7",
			$sformatf("[%0t] MD_A7: threshold==0 but motion_detected did NOT trigger for diff=%0d", $time, pixel_diff));
	  end
	end

	// --------------------------------------------------
	// [8] Illegal inputs sanity check
	// variance==0 means ANY bg_diff >=0 passes variance gating
	// --------------------------------------------------
	always @(posedge clk) begin
	  if (!rst && enable && (variance == 0) && (pixel_diff > threshold)) begin
		#1;
		assert (motion_detected)
		  else `uvm_fatal("MD_A8",
			$sformatf("[%0t] MD_A8: variance==0 but motion_detected did NOT trigger for diff=%0d", $time, pixel_diff));
	  end
	end

  `endif // ENABLE_MD_ASSERTIONS
  `endif // SYNTHESIS



endmodule: motion_detector
