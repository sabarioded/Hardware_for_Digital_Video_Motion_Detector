/*------------------------------------------------------------------------------
 * File          : box_filter_assertions.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module box_filter_assertions (
	input  logic        clk,
	input  logic        rst,
	input  logic        enable,
	input  logic [3:0]  neighbors_number,
	input  logic [8:0]  motion_map,
	input  logic        filtered_motion
);

	logic [4:0] number_of_motion_pixels;

	// Count the number of 1s in motion_map (Hamming weight)
	assign number_of_motion_pixels = motion_map[0] + motion_map[1] + motion_map[2] +
									 motion_map[3] + motion_map[4] + motion_map[5] +
									 motion_map[6] + motion_map[7] + motion_map[8];

	// === [1] Motion should be detected when count > neighbors_number
	property motion_detected_correct;
		@(posedge clk) disable iff (rst || !enable)
		(number_of_motion_pixels > neighbors_number) |-> ##1 filtered_motion;
	endproperty
	assert property (motion_detected_correct)
		else $error("filtered_motion should be HIGH (motion count > neighbors_number)");

	// === [2] Motion should NOT be detected when count <= neighbors_number
	property motion_not_detected_correct;
		@(posedge clk) disable iff (rst || !enable)
		(number_of_motion_pixels <= neighbors_number) |-> ##1 !filtered_motion;
	endproperty
	assert property (motion_not_detected_correct)
		else $error("filtered_motion should be LOW (motion count <= neighbors_number)");

endmodule
