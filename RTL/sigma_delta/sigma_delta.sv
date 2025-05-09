/*------------------------------------------------------------------------------
 * File          : sigma_delta_update.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 5, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module sigma_delta (
	input  logic        clk,
	input  logic        rst,
	input  logic        enable,
	input  logic		wr_background, 
	input  logic [7:0]  curr_pixel,
	input  logic [7:0]  background,
	input  logic [7:0]  variance,
	output logic [7:0]  background_next,
	output logic [7:0]  variance_next
);

	logic [7:0] diff; 
	assign diff = (curr_pixel > background) ? (curr_pixel - background) :
												(background - curr_pixel);

	always_ff @(posedge clk or posedge rst) begin
		if (rst || !enable) begin
			background_next <= 8'd0;
			variance_next   <= 8'd2;
		end else if (enable) begin
			// directly update the background during initialization 
			if(wr_background) begin
				background_next <= curr_pixel;
			end
			// Background update: approach current pixel
			else if (curr_pixel > background)
				background_next <= (background == 8'd255) ? 8'd255 : background + 1;
			else if (curr_pixel < background)
				background_next <= (background == 8'd0) ? 8'd0 : background - 1;
			else
				background_next <= background;

			// Variance update: increase if diff > variance, decrease if diff < variance
			if (diff > variance)
				variance_next <= (variance > 253) ? 8'd255 : variance + 2;
			else if (diff < variance)
				variance_next <= (variance < 4) ? 8'd2 : variance - 2;
			else
				variance_next <= variance;
		end
	end
	
endmodule
