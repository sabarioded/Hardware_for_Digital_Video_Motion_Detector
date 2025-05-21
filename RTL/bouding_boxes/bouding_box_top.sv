/*------------------------------------------------------------------------------
 * File          : bouding_box_top.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 12, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module bounding_box_top #(
	parameter WIDTH_BITS = 11,
	parameter HEIGHT_BITS = 10,
	parameter LABEL_WIDTH = 6,
	parameter NUM_LABELS = 1 << LABEL_WIDTH
)(
	input  logic clk,
	input  logic rst,
	input  logic enable,

	// Streaming input
	input  logic motion_pixel,
	input  logic last_in_frame,

	// Frame size
	input  logic [WIDTH_BITS-1:0]  width,
	input  logic [HEIGHT_BITS-1:0] height,

	// Bounding box outputs
	output logic bbox_valid,
	output logic [LABEL_WIDTH-1:0] bbox_label,
	output logic [WIDTH_BITS-1:0] bbox_min_x,
	output logic [HEIGHT_BITS-1:0] bbox_min_y,
	output logic [WIDTH_BITS-1:0] bbox_max_x,
	output logic [HEIGHT_BITS-1:0] bbox_max_y
);

	// Internal pixel coordinate trackers
	logic [WIDTH_BITS-1:0]  x;
	logic [HEIGHT_BITS-1:0] y;

	always_ff @(posedge clk or posedge rst) begin
		if (rst) begin
			x <= 0;
			y <= 0;
		end else if (enable) begin
			if (last_in_frame) begin
				x <= 0;
				y <= 0;
			end else if (x == width - 1) begin
				x <= 0;
				y <= y + 1;
			end else begin
				x <= x + 1;
			end
		end
	end

	// === Internal wires ===
	logic [LABEL_WIDTH-1:0] left_label;
	logic [LABEL_WIDTH-1:0] top_label;
	logic [LABEL_WIDTH-1:0] labeler_label;
	logic new_label_valid;
	logic [LABEL_WIDTH-1:0] new_label_value;
	logic merge_labels;
	logic [LABEL_WIDTH-1:0] merge_a, merge_b;
	logic [LABEL_WIDTH-1:0] resolved_label;

	logic [LABEL_WIDTH-1:0] label_line[0:MAX_WIDTH]; // adjust to maximum expected WIDTH

	always_ff @(posedge clk or posedge rst) begin
		if (rst) begin
			for (int i = 0; i < MAX_WIDTH; i++) label_line[i] <= 0;
		end else if (enable) begin
			label_line[x] <= resolved_label;
		end
	end

	assign left_label = (x == 0) ? 0 : label_line[x - 1];
	assign top_label  = label_line[x];

	// Labeler
	labeler #(.LABEL_WIDTH(LABEL_WIDTH)) labeler_inst (
		.clk(clk), .rst(rst), .enable(enable), .motion_pixel(motion_pixel),
		.left_label(left_label), .top_label(top_label),
		.new_label_valid(new_label_valid), .new_label_value(new_label_value),
		.merge_labels(merge_labels), .merge_a(merge_a), .merge_b(merge_b),
		.current_label(labeler_label)
	);

	// Merger
	label_merger #(.LABEL_WIDTH(LABEL_WIDTH), .NUM_LABELS(NUM_LABELS)) merger_inst (
		.clk(clk), .rst(rst),
		.merge_valid(merge_labels), .merge_a(merge_a), .merge_b(merge_b),
		.resolve_valid(enable && motion_pixel),
		.resolve_label(labeler_label), .resolved_label(resolved_label)
	);

	// Bounding Box Tracker
	logic [WIDTH_BITS-1:0]  min_x [NUM_LABELS];
	logic [HEIGHT_BITS-1:0] min_y [NUM_LABELS];
	logic [WIDTH_BITS-1:0]  max_x [NUM_LABELS];
	logic [HEIGHT_BITS-1:0] max_y [NUM_LABELS];
	logic [NUM_LABELS-1:0]  label_active;

	always_ff @(posedge clk or posedge rst) begin
		if (rst) begin
			for (int i = 0; i < NUM_LABELS; i++) begin
				min_x[i] <= '1;  // Max possible (for min tracking)
				min_y[i] <= '1;
				max_x[i] <= 0;
				max_y[i] <= 0;
				label_active[i] <= 0;
			end
		end else if (enable) begin
			if (new_label_valid) begin
				// Initialize on first hit
				min_x[new_label_value] <= x;
				max_x[new_label_value] <= x;
				min_y[new_label_value] <= y;
				max_y[new_label_value] <= y;
				label_active[new_label_value] <= 1;
			end else if(label_active[resolved_label]) begin
				// Update existing bounding box
				if (x < min_x[resolved_label]) min_x[resolved_label] <= x;
				if (x > max_x[resolved_label]) max_x[resolved_label] <= x;
				if (y < min_y[resolved_label]) min_y[resolved_label] <= y;
				if (y > max_y[resolved_label]) max_y[resolved_label] <= y;
			end
		end
	end

	typedef enum logic [1:0] {
		IDLE,
		OUTPUTTING,
		DONE
	} state_t;

	state_t state;
	logic [LABEL_WIDTH-1:0] label_idx;

	always_ff @(posedge clk or posedge rst) begin
		if (rst) begin
			state <= IDLE;
			label_idx <= 0;
			bbox_valid <= 0;
			bbox_label <= 0;
			bbox_min_x <= 0;
			bbox_min_y <= 0;
			bbox_max_x <= 0;
			bbox_max_y <= 0;
		end else begin
			case (state)
				IDLE: begin
					if (last_in_frame) begin
						label_idx <= 0;
						state <= OUTPUTTING;
					end
					bbox_valid <= 0;
				end

				OUTPUTTING: begin
					if (label_idx < NUM_LABELS) begin
						if (label_active[label_idx]) begin
							bbox_label   <= label_idx;
							bbox_min_x   <= min_x[label_idx];
							bbox_min_y   <= min_y[label_idx];
							bbox_max_x   <= max_x[label_idx];
							bbox_max_y   <= max_y[label_idx];
							bbox_valid   <= 1;
						end else begin
							bbox_valid <= 0;
						end
						label_idx <= label_idx + 1;
					end else begin
						state <= DONE;
						bbox_valid <= 0;
					end
				end

				DONE: begin
					// Wait for next frame_done pulse
					bbox_valid <= 0;
					if (!last_in_frame) begin
						state <= IDLE;
					end
				end
			endcase
		end
	end

endmodule
