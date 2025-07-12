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
	if (rst || !enable) begin
	  motion_detected <= 1'b0;
	end else begin
	  motion_detected <= (pixel_diff > threshold) && (background_diff >= variance);
	end
  end

// Assertions (ignored during synthesis)
`ifndef SYNTHESIS
`ifdef ENABLE_MD_ASSERTIONS

  // [1] After reset, motion_detected should be low.
  always @(posedge clk) begin
	if (rst) begin
	  #1;
	  assert (!motion_detected)
		else `uvm_fatal("MD_A1",
			 $sformatf("[%0t] MD_A1: motion_detected=%0d not low after reset",
					   $time, motion_detected));
	end
  end

  // [2] When enable is low, motion_detected should remain low.
  always @(posedge clk) begin
	if (!rst && !enable) begin
	  #1;
	  assert (!motion_detected)
		else `uvm_fatal("MD_A2",
			 $sformatf("[%0t] MD_A2: motion_detected=%0d changed when enable low",
					   $time, motion_detected));
	end
  end

  // [3] Motion detected condition
  always @(posedge clk) begin
	if (!rst && enable && (pixel_diff > threshold) && (background_diff >= variance)) begin
	  #1;
	  assert (motion_detected)
		else `uvm_fatal("MD_A3",
			 $sformatf("[%0t] MD_A3: motion_detected=%0d not asserted for pixel_diff=%0d background_diff=%0d",
					   $time, motion_detected, pixel_diff, background_diff));
	end
  end

  // [4] No-motion condition
  always @(posedge clk) begin
	if (!rst && enable && ((!(pixel_diff > threshold) || !(background_diff >= variance)))) begin
	  #1;
	  assert (!motion_detected)
		else `uvm_fatal("MD_A4",
			 $sformatf("[%0t] MD_A4: motion_detected=%0d asserted incorrectly for pixel_diff=%0d background_diff=%0d",
					   $time, motion_detected, pixel_diff, background_diff));
	end
  end

`endif // ENABLE_MD_ASSERTIONS
`endif // SYNTHESIS


endmodule: motion_detector
