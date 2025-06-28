/*------------------------------------------------------------------------------
 * File          : motion_highlight.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 31, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module motion_highlight #(
	parameter WIDTH_BITS  = 11,
	parameter HEIGHT_BITS = 10,
	parameter LABEL_WIDTH = 8,
	parameter NUM_LABELS  = 1 << LABEL_WIDTH,
	parameter MAX_WIDTH   = 1 << WIDTH_BITS
) (
	input  logic                     clk,
	input  logic                     rst,
	input  logic                     enable,

	input  logic [31:0]              rbg_pixel,

	input  logic                     bbox_valid,
	input  logic [LABEL_WIDTH-1:0]   bbox_label,
	input  logic [LABEL_WIDTH-1:0]   bbox_parent,
	input  logic [WIDTH_BITS-1:0]    bbox_min_x,
	input  logic [HEIGHT_BITS-1:0]   bbox_min_y,
	input  logic [WIDTH_BITS-1:0]    bbox_max_x,
	input  logic [HEIGHT_BITS-1:0]   bbox_max_y,

	// Frame size
	input  logic                     last_in_frame,
	input  logic [WIDTH_BITS-1:0]    width,
	input  logic [HEIGHT_BITS-1:0]   height,

	output logic [31:0]              highlighted_pixel,
	output logic                     pixel_valid
);

// Internal signals
logic bank_select;
logic transmission_done;
logic [LABEL_WIDTH-1:0] label_indx;
logic [WIDTH_BITS-1:0]  x;
logic [HEIGHT_BITS-1:0] y;

// Bounding-box storage
typedef struct packed {
	logic [WIDTH_BITS-1:0]  min_x;
	logic [HEIGHT_BITS-1:0] min_y;
	logic [WIDTH_BITS-1:0]  max_x;
	logic [HEIGHT_BITS-1:0] max_y;
	logic                   label_active;
} bbox_t;

bbox_t bank0 [NUM_LABELS];
bbox_t bank1 [NUM_LABELS];

// Descriptor receive FSM
typedef enum logic { IDLE, RECEIVING, FINISH_RECEIVING } state_t;
state_t state;

always_ff @(posedge clk or posedge rst) begin
	if (rst) begin
		state             <= IDLE;
		transmission_done <= 1'b0;
		label_indx        <= '0;
	end else if (enable) begin
		case (state)
			IDLE: begin
				if (last_in_frame)
					state <= RECEIVING;
				transmission_done <= 1'b0;
				label_indx        <= '0;
			end

			RECEIVING: begin
				if (bbox_label == 1) begin
					state             <= FINISH_RECEIVING;
					transmission_done <= 1'b1;
				end
			end

			FINISH_RECEIVING: begin
				case (bank_select)
					1'b0: begin
						bank1[label_indx].min_x        <= '1;
						bank1[label_indx].min_y        <= '1;
						bank1[label_indx].max_x        <= 0;
						bank1[label_indx].max_y        <= 0;
						bank1[label_indx].label_active <= 0;
					end
					1'b1: begin
						bank0[label_indx].min_x        <= '1;
						bank0[label_indx].min_y        <= '1;
						bank0[label_indx].max_x        <= 0;
						bank0[label_indx].max_y        <= 0;
						bank0[label_indx].label_active <= 0;
					end
				endcase

				label_indx <= label_indx + 1;
				if (label_indx == 255)
					state <= IDLE;
			end

			default: state <= IDLE;
		endcase
	end else begin
		state             <= IDLE;
		transmission_done <= 1'b0;
	end
end

// Coordinate generator
always_ff @(posedge clk or posedge rst) begin
	if (rst) begin
		x <= 0;
		y <= 0;
	end else if (enable) begin
		if (transmission_done) begin
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

// Bank select toggle
always_ff @(posedge clk or posedge rst) begin
	if (rst) begin
		bank_select <= 1'b0;
	end else if (enable && transmission_done) begin
		bank_select <= ~bank_select;
	end
end

// Update active bank
always_ff @(posedge clk or rst) begin
	if (rst) begin
		for (int i = 0; i < NUM_LABELS; i++) begin
			bank0[i].min_x        <= '1;
			bank0[i].min_y        <= '1;
			bank0[i].max_x        <= 0;
			bank0[i].max_y        <= 0;
			bank0[i].label_active <= 0;

			bank1[i].min_x        <= '1;
			bank1[i].min_y        <= '1;
			bank1[i].max_x        <= 0;
			bank1[i].max_y        <= 0;
			bank1[i].label_active <= 0;
		end
	end else if (enable && (state == RECEIVING) && bbox_valid) begin
		if (bank_select == 1'b0) begin
			if (bbox_min_x < bank0[bbox_parent].min_x)
				bank0[bbox_parent].min_x <= bbox_min_x;
			if (bbox_max_x > bank0[bbox_parent].max_x)
				bank0[bbox_parent].max_x <= bbox_max_x;
			if (bbox_min_y < bank0[bbox_parent].min_y)
				bank0[bbox_parent].min_y <= bbox_min_y;
			if (bbox_max_y > bank0[bbox_parent].max_y)
				bank0[bbox_parent].max_y <= bbox_max_y;
			bank0[bbox_label].label_active <= (bbox_label == bbox_parent) ? 1 : 0;
		end else begin
			if (bbox_min_x < bank1[bbox_parent].min_x)
				bank1[bbox_parent].min_x <= bbox_min_x;
			if (bbox_max_x > bank1[bbox_parent].max_x)
				bank1[bbox_parent].max_x <= bbox_max_x;
			if (bbox_min_y < bank1[bbox_parent].min_y)
				bank1[bbox_parent].min_y <= bbox_min_y;
			if (bbox_max_y > bank1[bbox_parent].max_y)
				bank1[bbox_parent].max_y <= bbox_max_y;
			bank1[bbox_label].label_active <= (bbox_label == bbox_parent) ? 1 : 0;
		end
	end
end

// -------------------------------------------------------------------------
// Output FSM: stream from inactive bank
// -------------------------------------------------------------------------
typedef enum logic { IDLE, OUTPUTTING } state_t;
state_t state;

logic on_any_bbox_edge;
bbox_s inactive_bank [NUM_LABELS];

always_comb begin
	on_any_bbox_edge = 1'b0;

	// Select the inactive bank
	case (bank_select)
		1'b0: inactive_bank = bank1;
		1'b1: inactive_bank = bank0;
		default: inactive_bank = bank0;
	endcase

	for (int i = 1; i < NUM_LABELS; i++) begin
		if (inactive_bank[i].label_active) begin
			if (((x == inactive_bank[i].min_x || x == inactive_bank[i].max_x) &&
				 (inactive_bank[i].min_y <= y && y <= inactive_bank[i].max_y)) ||
				((y == inactive_bank[i].min_y || y == inactive_bank[i].max_y) &&
				 (inactive_bank[i].min_x <= x && x <= inactive_bank[i].max_x))) begin
				on_any_bbox_edge = 1'b1;
			end
		end
	end
end

always_ff @(posedge clk or posedge rst) begin
	if (rst) begin
		state             <= IDLE;
		highlighted_pixel <= '0;
		pixel_valid       <= 1'b0;
	end else begin
		case (state)
			IDLE: begin
				if (transmission_done)
					state <= OUTPUTTING;
				highlighted_pixel <= '0;
				pixel_valid       <= 1'b0;
			end

			OUTPUTTING: begin
				if (on_any_bbox_edge)
					highlighted_pixel <= HIGHLIGHT_COLOR;
				else
					highlighted_pixel <= rbg_pixel;

				pixel_valid <= 1'b1;

				if (!enable)
					state <= IDLE;
			end

			default: begin
				state             <= IDLE;
				highlighted_pixel <= '0;
				pixel_valid       <= 1'b0;
			end
		endcase
	end
end

endmodule
