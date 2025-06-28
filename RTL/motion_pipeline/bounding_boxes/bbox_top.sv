/*------------------------------------------------------------------------------
 * File          : bounding_box_top.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 12, 2025
 * Description   : Pipelined, ping-pong bounding box top module (fixed)
 *------------------------------------------------------------------------------*/

module bbox_top #(
	parameter WIDTH_BITS  = 11,
	parameter HEIGHT_BITS = 10,
	parameter LABEL_WIDTH = 8,
	parameter NUM_LABELS  = 1 << LABEL_WIDTH,
	parameter MAX_WIDTH   = 1 << WIDTH_BITS
)(
	input  logic                         clk,
	input  logic                         rst,
	input  logic                         enable,

	// Streaming input
	input  logic                         motion_pixel,
	input  logic                         last_in_frame,

	// Frame size
	input  logic [WIDTH_BITS-1:0]       width,
	input  logic [HEIGHT_BITS-1:0]      height,

	// Bounding box outputs (streaming)
	output logic                         bbox_valid,
	output logic [LABEL_WIDTH-1:0]      bbox_label,
	output logic [LABEL_WIDTH-1:0]      bbox_parent,
	output logic [WIDTH_BITS-1:0]       bbox_min_x,
	output logic [HEIGHT_BITS-1:0]      bbox_min_y,
	output logic [WIDTH_BITS-1:0]       bbox_max_x,
	output logic [HEIGHT_BITS-1:0]      bbox_max_y
);

// -------------------------------------------------------------------------
// Coordinate generation
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

// -------------------------------------------------------------------------
// Stage 1: Labeler + line buffer
logic [LABEL_WIDTH-1:0] left_label, top_label;
logic [LABEL_WIDTH-1:0] label_line [0:MAX_WIDTH-1];

assign left_label = (x == 0) ? 0 : label_line[x - 1];
assign top_label  = label_line[x];

// Labeler outputs
logic                    new_label_valid;
logic [LABEL_WIDTH-1:0]  new_label_value;
logic                    merge_labels;
logic [LABEL_WIDTH-1:0]  merge_a, merge_b;
logic [LABEL_WIDTH-1:0]  current_label;

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

// -------------------------------------------------------------------------
// Stage 2: Merger
logic [LABEL_WIDTH-1:0] resolved_label;

label_merger #(
	.LABEL_WIDTH(LABEL_WIDTH)
) merger_inst(
	.clk(clk), .rst(rst), .enable(enable),
	.last_in_frame(last_in_frame), .merge_valid(merge_labels),
	.merge_a(merge_a), .merge_b(merge_b),
	.resolve_valid(motion_pixel),
	.resolve_label(current_label),
	.resolved_label(resolved_label)
);

// reset and update line buffer
always_ff @(posedge clk or posedge rst) begin
	if (rst) begin
		for (int i = 0; i < MAX_WIDTH; i++)
			label_line[i] <= 0;
	end else if (enable) begin
		if(motion_pixel) begin
			label_line[x] <=  resolved_label;
		end else begin
			label_line[x] <= '0;
		end
		if(last_in_frame) begin
			for (int i = 0; i < MAX_WIDTH; i++)
				label_line[i] <= 0;
		end
	end
end

// -------------------------------------------------------------------------
logic bank_select;
typedef struct packed {
	logic [WIDTH_BITS-1:0]  min_x;
	logic [HEIGHT_BITS-1:0] min_y;
	logic [WIDTH_BITS-1:0]  max_x;
	logic [HEIGHT_BITS-1:0] max_y;
	logic                   label_active;
	logic [LABEL_WIDTH-1:0] parent;
} bbox_s;

bbox_s bank0 [NUM_LABELS], bank1 [NUM_LABELS];

always_ff@(posedge clk or posedge rst) begin
	if(rst) begin
		bank_select <= 1'b0;
	end else if(enable && last_in_frame) begin
		bank_select <= ~bank_select;
	end
end

// Per-label bounding box updates
always_ff @(posedge clk or posedge rst) begin
	if (rst) begin
		for (int i = 0; i < NUM_LABELS; i++) begin
			bank0[i].min_x <= '1;  // Max possible (for min tracking)
			bank0[i].min_y <= '1;
			bank0[i].max_x <= 0;
			bank0[i].max_y <= 0;
			bank0[i].label_active <= 0;
			bank0[i].parent <= 0;
			
			bank1[i].min_x <= '1;  // Max possible (for min tracking)
			bank1[i].min_y <= '1;
			bank1[i].max_x <= 0;
			bank1[i].max_y <= 0;
			bank1[i].label_active <= 0;
			bank1[i].parent <= 0;
		end
	end else if (enable) begin
		if (last_in_frame) begin
			if (bank_select) begin // bank_select is 1, so bank0 was selected for output. Clear bank0.
				for (int i = 0; i < NUM_LABELS; i++) begin
					bank0[i].min_x <= '1;
					bank0[i].min_y <= '1;
					bank0[i].max_x <= 0;
					bank0[i].max_y <= 0;
					bank0[i].label_active <= 0;
					bank0[i].parent <= 0;
				end
			end else begin // bank_select is 0, so bank1 was selected for output. Clear bank1.
				for (int i = 0; i < NUM_LABELS; i++) begin
					bank1[i].min_x <= '1;
					bank1[i].min_y <= '1;
					bank1[i].max_x <= 0;
					bank1[i].max_y <= 0;
					bank1[i].label_active <= 0;
					bank1[i].parent <= 0;
				end
			end
		end
		
		if(bank_select && motion_pixel) begin
			if (!bank1[resolved_label].label_active) begin
				// Initialize on first hit
				bank1[resolved_label].min_x <= x;
				bank1[resolved_label].max_x <= x;
				bank1[resolved_label].min_y <= y;
				bank1[resolved_label].max_y <= y;
				bank1[resolved_label].label_active <= 1;
			end else begin
				// Update existing bounding box
				if (x < bank1[resolved_label].min_x) bank1[resolved_label].min_x <= x;
				if (x > bank1[resolved_label].max_x) bank1[resolved_label].max_x <= x;
				if (y < bank1[resolved_label].min_y) bank1[resolved_label].min_y <= y;
				if (y > bank1[resolved_label].max_y) bank1[resolved_label].max_y <= y;
			end
			bank1[current_label].parent <= resolved_label;
		end else if(!bank_select && motion_pixel) begin
			if (!bank0[resolved_label].label_active) begin
				// Initialize on first hit
				bank0[resolved_label].min_x <= x;
				bank0[resolved_label].max_x <= x;
				bank0[resolved_label].min_y <= y;
				bank0[resolved_label].max_y <= y;
				bank0[resolved_label].label_active <= 1;
			end else begin
				// Update existing bounding box
				if (x < bank0[resolved_label].min_x) bank0[resolved_label].min_x <= x;
				if (x > bank0[resolved_label].max_x) bank0[resolved_label].max_x <= x;
				if (y < bank0[resolved_label].min_y) bank0[resolved_label].min_y <= y;
				if (y > bank0[resolved_label].max_y) bank0[resolved_label].max_y <= y;
			end
			bank0[current_label].parent <= resolved_label;
		end
		
	end
end

// -------------------------------------------------------------------------
// Output FSM: stream from inactive bank
typedef enum logic {
IDLE,
OUTPUTTING
} state_t;

state_t state;
logic [LABEL_WIDTH-1:0] label_idx;

always_ff @(posedge clk or posedge rst) begin
if (rst) begin
	state <= IDLE;
	label_idx <= 255;
	bbox_valid <= 0;
	bbox_label   <= 0;
	bbox_min_x   <= 0;
	bbox_min_y   <= 0;
	bbox_max_x   <= 0;
	bbox_max_y   <= 0;
end else begin
	case (state)
		IDLE: begin
			if (last_in_frame) begin
				state <= OUTPUTTING;
			end
			label_idx <= 255;
			bbox_valid <= 0;
			bbox_label   <= 0;
			bbox_min_x   <= 0;
			bbox_min_y   <= 0;
			bbox_max_x   <= 0;
			bbox_max_y   <= 0;
		end

		OUTPUTTING: begin
			if(bank_select) begin
				if (bank0[label_idx].label_active) begin
					bbox_label   <= label_idx;
					bbox_min_x   <= bank0[label_idx].min_x;
					bbox_min_y   <= bank0[label_idx].min_y;
					bbox_max_x   <= bank0[label_idx].max_x;
					bbox_max_y   <= bank0[label_idx].max_y;
					bbox_valid   <= 1;
					bbox_parent <= bank0[label_idx].parent;
				end else bbox_valid   <= '0;
			end else begin
				if (bank1[label_idx].label_active) begin
					bbox_label   <= label_idx;
					bbox_min_x   <= bank1[label_idx].min_x;
					bbox_min_y   <= bank1[label_idx].min_y;
					bbox_max_x   <= bank1[label_idx].max_x;
					bbox_max_y   <= bank1[label_idx].max_y;
					bbox_valid   <= 1;
					bbox_parent <= bank1[label_idx].parent;
				end else bbox_valid   <= '0;
			end
			label_idx <= label_idx - 1;
			if(label_idx == 1) begin
				state <= IDLE;
			end
		end
		default: begin
			bbox_label   <= '0;
			bbox_min_x   <= '0;
			bbox_min_y   <= '0;
			bbox_max_x   <= '0;
			bbox_max_y   <= '0;
			bbox_valid   <= 0;
			bbox_parent <= '0;
		end
	endcase
end
end


endmodule
