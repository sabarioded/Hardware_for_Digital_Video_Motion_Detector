/*------------------------------------------------------------------------------
 * File           : bounding_box_top.sv
 * Project        : RTL
 * Author         : eposmk
 * Creation date  : May 12, 2025
 * Description    : Pipelined, ping-pong bounding box top module (updated)
 *------------------------------------------------------------------------------*/

module bbox_top #(
	parameter WIDTH_BITS  = 11,
	parameter HEIGHT_BITS = 10,
	parameter LABEL_WIDTH = 8,
	parameter NUM_LABELS  = 1 << LABEL_WIDTH,
	parameter MAX_WIDTH   = 1 << WIDTH_BITS,
	parameter HIGHLIGHT_COLOR = 32'hFF000000
)(
	input  logic clk,
	input  logic rst,
	input  logic enable,

	// Streaming input
	input  logic motion_pixel,
	input  logic last_in_frame,
	input  logic [31:0] rgb_pixel,

	// Frame size
	input  logic [WIDTH_BITS-1:0] width,
	input  logic [HEIGHT_BITS-1:0] height,

	// Bounding box outputs (streaming)
	output logic [31:0] highlighted_pixel,
	output logic pixel_valid
	
	// DEBUG
	/*,
	output logic [WIDTH_BITS-1:0] x_out,
	output logic [HEIGHT_BITS-1:0] y_out
	// END DEBUG
	*/
);
localparam int PROX = 5; 
// -------------------------------------------------------------------------
// Coordinate generation
// Generates the current pixel's X and Y coordinates within the frame.
// X increments per clock, Y increments when X reaches 'width - 1'.
// Both reset at the start of a new frame (last_in_frame).
logic [WIDTH_BITS-1:0] x;
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

	// -------------------------------------------------------------------------
	// Stage 1: Labeler + Line Buffer
	// This stage assigns labels to connected motion pixels and stores labels
	// for the previous row to determine vertical connectivity.
	logic [LABEL_WIDTH-1:0] left_label, top_label;
	logic [LABEL_WIDTH-1:0] label_line [0:MAX_WIDTH-1]; // Stores labels of the previous row

	// Determine left and top labels for the current pixel.
	// left_label is the label of the pixel to the left (x-1).
	// top_label is the label of the pixel directly above (from the line buffer).
	assign left_label = (x == 0) ? 0 : label_line[x - 1];
	assign top_label  = label_line[x];

	// Labeler outputs (from the assumed external 'labeler' submodule)
	logic new_label_valid;
	logic [LABEL_WIDTH-1:0] new_label_value;
	logic merge_labels;
	logic [LABEL_WIDTH-1:0] merge_a, merge_b;
	logic [LABEL_WIDTH-1:0] current_label; // The label assigned by the labeler before merger resolution
	logic [LABEL_WIDTH-1:0] resolved_label; // The final resolved label after merger

	// Instantiate the 'labeler' submodule. This module is assumed to be defined elsewhere.
	labeler #(.LABEL_WIDTH(LABEL_WIDTH)) labeler_inst(
		.clk(clk), .rst(rst), .enable(enable),
		.last_in_frame(last_in_frame), .motion_pixel(motion_pixel),
		.left_label(left_label), .top_label(top_label),
		.new_label_valid(new_label_valid),
		.new_label_value(new_label_value),
		.merge_labels(merge_labels),
		.merge_a(merge_a), .merge_b(merge_b),
		.current_label(current_label)
	);

	// Update and reset the line buffer.
	// If it's a motion pixel, store its resolved label.
	// If not a motion pixel, clear the entry.
	// Reset the entire line buffer at the end of a frame.
	always_ff @(posedge clk or posedge rst) begin
		if (rst) begin
			for (int i = 0; i < MAX_WIDTH; i++)
				label_line[i] <= 0;
		end else if (enable) begin
			if(motion_pixel) begin
				label_line[x] <= resolved_label;
			end else begin
				label_line[x] <= '0; // Clear label if not a motion pixel
			end
			if(last_in_frame) begin
				// Reset line buffer at the end of a frame for the next frame
				for (int i = 0; i < MAX_WIDTH; i++)
					label_line[i] <= 0;
			end
		end
	end

	// -------------------------------------------------------------------------
	// Stage 2: Merger
	// This stage resolves merged labels, ensuring all connected components
	// ultimately share a single label.
	// The 'label_merger' submodule is assumed to be defined elsewhere.
	label_merger #(.LABEL_WIDTH(LABEL_WIDTH)) merger_inst(
		.clk(clk), .rst(rst), .enable(enable),
		.last_in_frame(last_in_frame),
		.merge_valid(merge_labels),      // Indicates labels need to be merged
		.merge_a(merge_a), .merge_b(merge_b), // Labels to merge
		.resolve_valid(motion_pixel),    // Request resolution for the current pixel's label
		.resolve_label(current_label),  // The label to resolve
		.resolved_label(resolved_label)  // The final, resolved label
	);
	
	// -------------------------------------------------------------------------
	// Bounding Box Storage Banks (Ping-Pong Buffering)
	// Four banks are used to pipeline bounding box updates, filtering, and output.
	logic [1:0] bank_select; // Controls which bank is currently being written to

	// Structure to hold bounding box coordinates and active status for a single label.
	typedef struct packed {
		logic [WIDTH_BITS-1:0]  min_x;
		logic [HEIGHT_BITS-1:0] min_y;
		logic [WIDTH_BITS-1:0]  max_x;
		logic [HEIGHT_BITS-1:0] max_y;
		logic                   label_active;
		logic is_root;
	} bbox_s;

	// Single 2D array to hold all four banks of bounding box data.
	bbox_s banks [4][NUM_LABELS];
	
	// FSM for cycling bank_select for writing.
	// At the end of each frame, the 'write' bank role shifts to the next bank.
	always_ff@(posedge clk or posedge rst) begin
		if(rst) begin
			bank_select <= 2'b00; // Start with bank0 for writing
		end else if(enable && last_in_frame) begin
			// Cycle the bank for the next frame's writing
			case(bank_select)
				2'b00: bank_select <= 2'b01; // Was writing to bank0, next write to bank1
				2'b01: bank_select <= 2'b10; // Was writing to bank1, next write to bank2
				2'b10: bank_select <= 2'b11; // Was writing to bank2, next write to bank3
				2'b11: bank_select <= 2'b00; // Was writing to bank3, next write to bank0
				default: bank_select <= 2'b00; // Safety
			endcase
		end
	end
	
	// Combinational logic to determine the index of the bank for each role.
	// This ensures a single driver for the 'banks' array.
	logic [1:0] input_bank_idx;
	logic [1:0] filter_bank_idx;
	logic [1:0] output_bank_idx;
	logic [1:0] clear_bank_idx;

	always_comb begin
		input_bank_idx  = bank_select;       // Current frame's write bank
		clear_bank_idx  = (bank_select + 2'b01) % 4; // Bank to be cleared (next frame's write bank)
		output_bank_idx = (bank_select + 2'b10) % 4; // Bank for current frame's output highlighting
		filter_bank_idx = (bank_select + 2'b11) % 4; // Bank for filtering (previous frame's data)
	end
	
	// -------------------------------------------------------------------------
	// Bounding Box Filtering Logic
	// This FSM manages the multi-cycle process of merging and eliminating
	// overlapping or contained bounding boxes in the 'filter_bank'.
	typedef enum logic {
		IDLE,   // Waiting for end of frame to start filtering
		FILTER  // Iterating through labels to filter
	} state_t;

		state_t filter_state;
		logic [LABEL_WIDTH-1:0] merge_i; // Outer loop index for filtering
		logic [LABEL_WIDTH-1:0] merge_j; // Inner loop index for filtering
		logic not_root;

		always_ff @(posedge clk or posedge rst) begin
		if (rst) begin
			filter_state <= IDLE;
			merge_i <= 1; // Start from label 1 (assuming 0 is reserved/background)
			merge_j <= 2; // Start from label 2
		end else begin
			case (filter_state)
				IDLE: begin
					if (last_in_frame) begin // Start filtering when current frame ends
						filter_state <= FILTER;
					end
					merge_i <= 1; // Reset indices for next filtering cycle
					merge_j <= 2;
				end

				FILTER: begin
					if (merge_i < NUM_LABELS-1) begin
						if (merge_j < NUM_LABELS-1 && !not_root) begin
							merge_j <= merge_j + 1; // Increment inner loop
							end else begin
							merge_i <= merge_i + 1; // Increment outer loop
							merge_j <= 1;//merge_i + 2; // Reset inner loop relative to outer
						end
					end else begin
						filter_state <= IDLE; // All labels processed, return to IDLE
					end
				end
				default: begin
					//filter_state <= IDLE; // Safety
				end
			endcase
		end
		end

	
	// -------------------------------------------------------------------------
	// Per-label Bounding Box Updates and Filtering Execution
	// This block handles:
	// 1. Initializing all banks on reset.
	// 2. Clearing the 'clear_bank' (one label per cycle) after a frame.
	// 3. Updating bounding box coordinates in the 'input_bank' for motion pixels.
	// 4. Executing the filtering logic on the 'filter_bank' when 'filter_state' is FILTER.
	logic [LABEL_WIDTH-1:0] clear_indx; // Index for clearing labels in the clear_bank

	always_ff @(posedge clk or posedge rst) begin
		if (rst) begin
			// Initialize all banks on reset to a known inactive state.
			for (int bank_idx = 0; bank_idx < 4; bank_idx++) begin
				for (int i = 0; i < NUM_LABELS; i++) begin
					banks[bank_idx][i].min_x <= '1;  // Max possible value (for min tracking)
					banks[bank_idx][i].min_y <= '1;
					banks[bank_idx][i].max_x <= 0;
					banks[bank_idx][i].max_y <= 0;
					banks[bank_idx][i].label_active <= 0;
					banks[bank_idx][i].is_root <= 0;
				end
			end
			clear_indx <= 0; // Initialize clear index
		end else if (enable) begin
			// Logic to clear the 'clear_bank' one label per cycle.
			// This process starts when 'last_in_frame' is asserted and continues for NUM_LABELS cycles.
			if (last_in_frame) begin
				clear_indx <= 1; // Start clearing from label 1 (assuming 0 is unused)
			end else if (clear_indx != 0 && clear_indx < NUM_LABELS) begin
				clear_indx <= clear_indx + 1;
			end else begin
				clear_indx <= 0; // Reset when clearing is done or not active
			end

			// Perform clearing if the clear_indx is valid and clearing is active.
			if (clear_indx != 0 && clear_indx < NUM_LABELS) begin
				banks[clear_bank_idx][clear_indx].min_x <= '1;
				banks[clear_bank_idx][clear_indx].min_y <= '1;
				banks[clear_bank_idx][clear_indx].max_x <= 0;
				banks[clear_bank_idx][clear_indx].max_y <= 0;
				banks[clear_bank_idx][clear_indx].label_active <= 0;
				banks[clear_bank_idx][clear_indx].is_root <= 0;
			end
			
			// Update the bounding box in the 'input_bank' for the current frame.
			// This happens for every motion pixel.
			if (motion_pixel) begin
				// If this is the first time this label is seen in the current frame, initialize its bbox.
				if (!banks[input_bank_idx][resolved_label].label_active) begin
					banks[input_bank_idx][resolved_label].min_x <= x;
					banks[input_bank_idx][resolved_label].max_x <= x;
					banks[input_bank_idx][resolved_label].min_y <= y;
					banks[input_bank_idx][resolved_label].max_y <= y;
					banks[input_bank_idx][resolved_label].label_active <= 1;
					banks[input_bank_idx][resolved_label].is_root <= 1;
				end else begin
					// Otherwise, update the existing bounding box to encompass the current pixel.
					if (x < banks[input_bank_idx][resolved_label].min_x) banks[input_bank_idx][resolved_label].min_x <= x;
					if (x > banks[input_bank_idx][resolved_label].max_x) banks[input_bank_idx][resolved_label].max_x <= x;
					if (y < banks[input_bank_idx][resolved_label].min_y) banks[input_bank_idx][resolved_label].min_y <= y;
					if (y > banks[input_bank_idx][resolved_label].max_y) banks[input_bank_idx][resolved_label].max_y <= y;
					banks[input_bank_idx][current_label].is_root <= (resolved_label == current_label) ? 1 : 0;
				end
			end
			/*
			if(clear_indx != 0 && banks[filter_bank_idx][clear_indx].label_active) begin
				$display("Time %0t: DEBUG_RECEIVE: OUT Bbox: label=%0d, Coords=(%0d,%0d)-(%0d,%0d), valid=%0d.",
					$time, clear_indx, banks[filter_bank_idx][clear_indx].min_x, banks[filter_bank_idx][clear_indx].min_y,
					banks[filter_bank_idx][clear_indx].max_x, banks[filter_bank_idx][clear_indx].max_y, banks[filter_bank_idx][clear_indx].label_active);
			end
			*/
			
			if (filter_state == FILTER
					&& merge_i < NUM_LABELS
					&& merge_j < NUM_LABELS
					&& merge_i != merge_j
					&& banks[filter_bank_idx][merge_i].label_active
					&& banks[filter_bank_idx][merge_j].label_active ) begin
				/*$display("Time %0t: (i,j) - (%0d,%0d).",
						$time, merge_i,merge_j );*/
					  if (!( banks[filter_bank_idx][merge_i].max_x + PROX < banks[filter_bank_idx][merge_j].min_x
								|| banks[filter_bank_idx][merge_i].min_x > banks[filter_bank_idx][merge_j].max_x + PROX
								|| banks[filter_bank_idx][merge_i].max_y + PROX < banks[filter_bank_idx][merge_j].min_y
								|| banks[filter_bank_idx][merge_i].min_y > banks[filter_bank_idx][merge_j].max_y +PROX)) begin

					// merge j into i (nonblocking)
					banks[filter_bank_idx][merge_i].min_x <= (banks[filter_bank_idx][merge_i].min_x < banks[filter_bank_idx][merge_j].min_x)
															? banks[filter_bank_idx][merge_i].min_x
															: banks[filter_bank_idx][merge_j].min_x;
					banks[filter_bank_idx][merge_i].min_y <= (banks[filter_bank_idx][merge_i].min_y < banks[filter_bank_idx][merge_j].min_y)
															? banks[filter_bank_idx][merge_i].min_y
															: banks[filter_bank_idx][merge_j].min_y;
					banks[filter_bank_idx][merge_i].max_x <= (banks[filter_bank_idx][merge_i].max_x > banks[filter_bank_idx][merge_j].max_x)
															? banks[filter_bank_idx][merge_i].max_x
															: banks[filter_bank_idx][merge_j].max_x;
					banks[filter_bank_idx][merge_i].max_y <= (banks[filter_bank_idx][merge_i].max_y > banks[filter_bank_idx][merge_j].max_y)
															? banks[filter_bank_idx][merge_i].max_y
															: banks[filter_bank_idx][merge_j].max_y;

					// now deactivate j
					banks[filter_bank_idx][merge_j].label_active <= 1'b0;
					/*$display("Time %0t: DEBUG_RECEIVE: MERGED Bbox: label i=%0d, label j=%0d , Coords i=(%0d,%0d)-(%0d,%0d), Coords j=(%0d,%0d)-(%0d,%0d).",
							$time, merge_i,merge_j, banks[filter_bank_idx][merge_i].min_x, banks[filter_bank_idx][merge_i].min_y,
							banks[filter_bank_idx][merge_i].max_x, banks[filter_bank_idx][merge_i].max_y, 
							banks[filter_bank_idx][merge_j].min_x, banks[filter_bank_idx][merge_j].min_y,
							banks[filter_bank_idx][merge_j].max_x, banks[filter_bank_idx][merge_j].max_y);*/ 
					  end
			end //FILTER

		end
	end
	
	always_comb begin
		if(!banks[filter_bank_idx][merge_i].is_root) begin
			not_root = 1;
		end else begin
			not_root = 0;
		end
	end

// -------------------------------------------------------------------------
// Output Highlighting Logic
// Determines if the current pixel falls on the edge of any active bounding box
// from the 'output_bank' (which contains filtered results from 2 frames ago).
logic on_any_bbox_edge;

always_comb begin
	on_any_bbox_edge = 1'b0; // Default to not on an edge

	// Iterate through all possible labels (excluding label 0, typically background).
	for (int i = 1; i < NUM_LABELS; i++) begin
		if (banks[output_bank_idx][i].label_active) begin // Only check active bounding boxes
				// Check if the current pixel (x,y) is on a vertical edge of bbox i.
				if ((x == banks[output_bank_idx][i].min_x || x == banks[output_bank_idx][i].max_x) &&
					(banks[output_bank_idx][i].min_y <= y && y <= banks[output_bank_idx][i].max_y)) begin
					on_any_bbox_edge = 1'b1;
				end
				// Check if the current pixel (x,y) is on a horizontal edge of bbox i.
				else if ((y == banks[output_bank_idx][i].min_y || y == banks[output_bank_idx][i].max_y) &&
							 (banks[output_bank_idx][i].min_x <= x && x <= banks[output_bank_idx][i].max_x)) begin
					on_any_bbox_edge = 1'b1;
				end
			end
		end
end

typedef enum logic [1:0] {
	IDLE_OUT,
	FILTERING,
	OUTPUTING
	
} state_out;

	state_out output_state;
	
	always_ff @(posedge clk or posedge rst) begin
		if(rst) begin
			output_state <= IDLE_OUT;
			highlighted_pixel <= '0;
			pixel_valid       <= 1'b0;
		end else if(enable) begin
			case (output_state)
				IDLE_OUT: begin
					if (last_in_frame) begin
						output_state <= FILTERING;
					end
				end
				FILTERING: begin
					if(!enable) begin
						output_state <= IDLE_OUT;
						end else if (last_in_frame) begin
						output_state <= OUTPUTING;
					end
				end
				OUTPUTING: begin
					highlighted_pixel <= on_any_bbox_edge ? HIGHLIGHT_COLOR : rgb_pixel;
					pixel_valid       <= 1'b1;
					// DEBUG
					/*
					if(clear_indx != 0 && banks[output_bank_idx][clear_indx].label_active) begin
						$display("Time %0t: DEBUG_RECEIVE: OUT Bbox: label=%0d, Coords=(%0d,%0d)-(%0d,%0d), valid=%0d.",
							$time, clear_indx, banks[output_bank_idx][clear_indx].min_x, banks[output_bank_idx][clear_indx].min_y,
							banks[output_bank_idx][clear_indx].max_x, banks[output_bank_idx][clear_indx].max_y, banks[output_bank_idx][clear_indx].label_active); 
					end
					*/
					// END DEBUG
					if (!enable) begin
						output_state <= IDLE_OUT;
					end
				end
				default: begin
					output_state <= IDLE_OUT;
					highlighted_pixel <= '0;
					pixel_valid       <= 1'b0;
				end
			endcase
		end
	end
	/*
// DEBUG
logic [WIDTH_BITS-1:0]  x_reg;
logic [HEIGHT_BITS-1:0] y_reg;
always_ff @(posedge clk or posedge rst) begin
	x_reg <= x;
	y_reg <= y;
end
assign x_out = x_reg;
assign y_out = y_reg;
// END DEBUG
*/
endmodule