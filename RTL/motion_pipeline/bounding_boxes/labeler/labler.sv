/*------------------------------------------------------------------------------
 * File          : labler.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 12, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module labeler #(
	parameter LABEL_WIDTH = 8  
)(
	input  logic               clk,
	input  logic               rst,
	input  logic               enable,
	input  logic			   last_in_frame,
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
		if (rst) begin
			next_label <= 1;  // Start labeling from 1
		end
		else if (enable) begin
			if(last_in_frame) begin
				next_label <= 1;
			end
			else if(motion_pixel && new_label_valid && next_label != 0) begin
				next_label <= next_label + 1;
				end
			end
	end

	always_comb begin
		current_label = 0;
		new_label_valid = 0;
		new_label_value = 0;
		merge_labels = 0;
		merge_a = 0;
		merge_b = 0;
		if(!rst) begin
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
	end
	
	
	`ifndef SYNTHESIS
	`ifdef ENABLE_LABLER_ASSERTIONS
	property new_label_isolated;
		@(posedge clk) disable iff (rst)
		(enable && motion_pixel && left_label == 0 && top_label == 0) |-> (new_label_valid && new_label_value == next_label && current_label == next_label);
	endproperty
	assert property(new_label_isolated) else $fatal(1, $sformatf("[%0t] new_label_isolated: failed to add new label", $time));

	property no_new_label;
		@(posedge clk) disable iff (rst)
		(enable && motion_pixel && (left_label != 0 || top_label != 0)) |-> (!new_label_valid);
	endproperty
	assert property(no_new_label) else $fatal(1, $sformatf("[%0t] no_new_label: added new label when shouldnt have", $time));

	property merge_two_neighbors_left;
		@(posedge clk) disable iff (rst)
		(enable && motion_pixel && left_label != 0 && top_label != 0 && left_label > top_label) |-> // Assuming 'right_label' is a valid input now
		(current_label == top_label && merge_labels == 1 && merge_a == top_label && merge_b == left_label);
	endproperty
	assert property(merge_two_neighbors_left) else $fatal(1, $sformatf("[%0t] merge_two_neighbors_left: failed to merge when left > top", $time));

	property merge_two_neighbors_top;
		@(posedge clk) disable iff (rst)
		(enable && motion_pixel && left_label != 0 && top_label != 0 && left_label < top_label) |->
		(current_label == left_label && merge_labels == 1 && merge_a == left_label && merge_b == top_label);
	endproperty
	assert property(merge_two_neighbors_top) else $fatal(1, $sformatf("[%0t] merge_two_neighbors_top: failed to merge when left < top", $time));

	property dont_merge_single_neighbor;
		@(posedge clk) disable iff (rst)
		(enable && motion_pixel && (left_label == 0 ^ top_label == 0)) |->
		(!merge_labels);
	endproperty
	assert property(dont_merge_single_neighbor) else $fatal(1, $sformatf("[%0t] dont_merge_single_neighbor: merged when shouldnt have", $time));

	property idle_outputs;
		@(posedge clk) disable iff (rst)
		((!enable || !motion_pixel))
		|-> (!new_label_valid && !merge_labels && current_label==0 && new_label_value==0 && merge_a==0 && merge_b==0);
	endproperty
	assert property (idle_outputs)
		else $fatal(1, $sformatf("[%0t] idle_outputs failed", $time));

	property next_label_increment;
		@(posedge clk) disable iff (rst)
		(enable && motion_pixel && new_label_valid && next_label != 0 && !last_in_frame)
		|-> ##1 (next_label == $past(next_label) + 1);
	endproperty
	assert property (next_label_increment)
		else $fatal(1, $sformatf("[%0t] next_label_increment failed", $time));

	property next_label_reset;
		@(posedge clk) disable iff (rst)
		(enable && last_in_frame)
		|-> ##1 (next_label == 1);
	endproperty
	assert property (next_label_reset)
		else $fatal(1, $sformatf("[%0t] next_label_reset failed", $time));

	`endif // ENABLE_LABLER_ASSERTIONS
	`endif // SYNTHESIS

endmodule
