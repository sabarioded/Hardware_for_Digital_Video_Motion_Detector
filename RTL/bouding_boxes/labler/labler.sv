/*------------------------------------------------------------------------------
 * File          : labler.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 12, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module labeler #(
	parameter LABEL_WIDTH = 6  // Supports up to 64 labels
)(
	input  logic               clk,
	input  logic               rst,
	input  logic               enable,     
	input  logic               motion_pixel,  // Current pixel is motion
	input  logic [LABEL_WIDTH-1:0] left_label,
	input  logic [LABEL_WIDTH-1:0] top_label,
	
	output logic               new_label_valid,   // Signal to allocate new label
	output logic [LABEL_WIDTH-1:0] new_label_value,

	output logic               merge_labels,    // Signal to label_merger
	output logic [LABEL_WIDTH-1:0] merge_a, // merge b into a
	output logic [LABEL_WIDTH-1:0] merge_b,

	output logic [LABEL_WIDTH-1:0] current_label   // Final label for this pixel
);

	logic [LABEL_WIDTH-1:0] next_label;
	always_ff @(posedge clk or posedge rst) begin
		if (rst)
			next_label <= 1;  // Start labeling from 1
		else if (enable && motion_pixel && new_label_valid)
			next_label <= next_label + 1;
	end

	always_comb begin
		current_label = 0;
		new_label_valid = 0;
		new_label_value = 0;
		merge_labels = 0;
		merge_a = 0;
		merge_b = 0;

		if (enable && motion_pixel) begin
			if (left_label == 0 && top_label == 0) begin
				// New isolated pixel
				new_label_valid = 1;
				new_label_value = next_label;
				current_label = next_label;
			end else if (left_label != 0 && top_label == 0) begin
				current_label = left_label;
			end else if (left_label == 0 && top_label != 0) begin
				current_label = top_label;
			end else begin
				// Both neighbors exist use smaller label
				if (left_label < top_label) begin
					current_label = left_label;
					merge_labels = 1;
					merge_a = left_label;
					merge_b = top_label;
				end else if (top_label < left_label) begin
					current_label = top_label;
					merge_labels = 1;
					merge_a = top_label;
					merge_b = left_label;
				end else begin
					current_label = left_label;  // Same label
				end
			end
		end
	end

endmodule
