/*------------------------------------------------------------------------------
 * File          : motion_detector_assertions.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module motion_detector_assertions (
	input  logic        clk,
	input  logic        rst,
	input  logic        enable,
	input  logic [7:0]  background,
	input  logic [7:0]  variance,
	input  logic [7:0]  curr_pixel,
	input  logic [7:0]  prev_pixel,
	input  logic [7:0]  threshold,
	input  logic        motion_detected
);

	logic [7:0] pixel_diff;
	logic [7:0] background_diff;

	assign pixel_diff = (curr_pixel > prev_pixel) ?
						(curr_pixel - prev_pixel) :
						(prev_pixel - curr_pixel);

	assign background_diff = (curr_pixel > background) ?
							 (curr_pixel - background) :
							 (background - curr_pixel);

	// === Assertions ===

	property motion_detected_valid;
		@(posedge clk) disable iff (rst || !enable)
		((pixel_diff > threshold) && (background_diff >= variance)) |-> ##1 motion_detected;
	endproperty
	assert property (motion_detected_valid)
		else $error("motion_detected should be HIGH");

	property motion_detected_clear;
		@(posedge clk) disable iff (rst || !enable)
		((pixel_diff <= threshold || background_diff < variance)) |-> ##1 !motion_detected;
	endproperty
	assert property (motion_detected_clear)
		else $error("motion_detected should be LOW");

endmodule
