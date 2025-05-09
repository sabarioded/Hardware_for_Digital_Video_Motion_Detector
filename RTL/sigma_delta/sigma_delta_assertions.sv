/*------------------------------------------------------------------------------
 * File          : sigma_delta_update_assertions.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 5, 2025
 * Description   : Assertions for sigma_delta_update module
 *------------------------------------------------------------------------------*/

module sigma_delta_assertions (
	input  logic        clk,
	input  logic        rst,
	input  logic        enable,
	input  logic        wr_background,
	input  logic [7:0]  curr_pixel,
	input  logic [7:0]  background,
	input  logic [7:0]  variance,
	input  logic [7:0]  background_next,
	input  logic [7:0]  variance_next
);

	// === Internal signal for diff computation ===
	logic [8:0] diff;
	assign diff = (curr_pixel > background) ? (curr_pixel - background) :
											   (background - curr_pixel);
	
	// === [1] Background overflow/underflow protection ===

	property background_increment_safe;
		@(posedge clk) disable iff (rst || !enable || wr_background)
		(curr_pixel > background && background == 8'd255) |-> (background_next == 8'd255);
	endproperty
	assert property (background_increment_safe)
		else $error("background_next overflow on increment!");

	property background_decrement_safe;
		@(posedge clk) disable iff (rst || !enable || wr_background)
		(curr_pixel < background && background == 8'd0) |-> (background_next == 8'd0);
	endproperty
	assert property (background_decrement_safe)
		else $error("background_next underflow on decrement!");

	// === [2] Variance bounds protection ===

	property variance_upper_bound_safe;
		@(posedge clk) disable iff (rst || !enable)
		(variance > 253 && curr_pixel != background) |-> (variance_next <= 8'd255);
	endproperty
	assert property (variance_upper_bound_safe)
		else $error("variance_next overflow!");

	property variance_lower_bound_safe;
		@(posedge clk) disable iff (rst || !enable)
		(variance < 4 && curr_pixel != background) |-> (variance_next >= 8'd2);
	endproperty
	assert property (variance_lower_bound_safe)
		else $error("variance_next underflow!");

	// === [3] Direct background write ===
		always @(posedge clk) begin
			if (!rst && enable && wr_background) begin
			  #1;
			  assert (background_next == curr_pixel)
				else $error("background_next != curr_pixel (1ns after wr_background)");
			end
		  end


endmodule
