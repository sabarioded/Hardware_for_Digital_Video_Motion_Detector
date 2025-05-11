/*------------------------------------------------------------------------------
 * File          : control.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 10, 2025
 * Description   : Pipelined control unit with AXI4-Lite config and stage control
 *------------------------------------------------------------------------------*/

module control (
	input  logic        clk,
	input  logic        rst,

	// AXI STREAM handshake
	input  logic        input_valid,
	input  logic        output_ready,
	output logic        axi_stream_valid;
	output logic        axi_stream_ready;


	// AXI STREAM input frame end
	input  logic        last,

	// AXI Lite config inputs
	input  logic        axi_lite_valid,
	output logic        axi_lite_ready,
	input  logic [10:0] width,
	input  logic [9:0]  height,
	input  logic [7:0]  threshold,

	// Configuration outputs
	output logic [10:0] cfg_width,
	output logic [9:0]  cfg_height,
	output logic [7:0]  cfg_threshold,

	// Control enables
	output logic        frame_manager_enb,
	output logic        sigma_delta_enb,
	output logic        motion_detector_enb,
	output logic        memory_manager_enb,
	output logic        box_filter_enb,
	output logic        motion_overlay_enb
);

// === Internal Registers ===
logic [10:0] width_reg;
logic [9:0]  height_reg;
logic [7:0]  threshold_reg;
logic        frame_done;

assign cfg_width     = width_reg;
assign cfg_height    = height_reg;
assign cfg_threshold = threshold_reg;

assign active = (input_valid && output_ready);
assign axi_stream_ready  = active;
assign axi_stream_valid  = stage_3_valid;

// Configuration update
assign axi_lite_ready = !active;

always_ff @(posedge clk or posedge rst) begin
	if (rst) begin
		width_reg     <= 11'd0;
		height_reg    <= 10'd0;
		threshold_reg <= 8'd0;
	end else if (axi_lite_valid && !active) begin
		width_reg     <= width;
		height_reg    <= height;
		threshold_reg <= threshold;
	end
end

logic [1:0] frame_counter;
always_ff @(posedge clk or posedge rst) begin
	if (rst)
		frame_counter <= 0;
	else if (last && active && frame_counter < 3)
		frame_counter <= frame_counter + 1;
end

// === FSM for Frame-Level Pipeline Control ===
typedef enum logic [1:0] {
	IDLE       = 2'd0,
	WAIT_2_FRM = 2'd1,
	RUN1       = 2'd2,
	RUN2       = 2'd3
} state_t;
state_t PS, NS;


always_ff@(posedge clk or posedge rst) begin
	if(rst) begin
		PS <= IDLE;
	end else begin
		PS <= NS;
	end
end

always_comb begin
	case(PS)
		IDLE: begin
			NS = active ? WAIT_2_FRM : IDLE;
			stage_1_valid = 0;
			stage_2_valid = 0;
			stage_3_valid = 0;
		end
		WAIT_2_FRM: begin
			NS = (active && frame_counter == 2) ? RUN1 :
					(active)      ? WAIT_2_FRM : IDLE; 
			stage_1_valid = 1;
			stage_2_valid = 0;
			stage_3_valid = 0;
		end
		RUN1: begin
			NS = (active && frame_counter == 3) ? RUN2 :
					(active)      ? RUN1 : IDLE; 
			stage_1_valid = active;
			stage_2_valid = active;
			stage_3_valid = 0;
		end
		RUN2: begin
			NS = (active) ? RUN2 : IDLE;
			stage_1_valid = active;
			stage_2_valid = active;
			stage_3_valid = active;
		end
		default: begin
			NS = IDLE;
			stage_1_valid = 0;
			stage_2_valid = 0;
			stage_3_valid = 0;
		end
	endcase
end

// === Stage Shift Pipeline ===
logic stage_1_valid, stage_2_valid,stage_3_valid;

// === Enable Signals ===
assign frame_manager_enb   = stage_1_valid;
assign sigma_delta_enb     = stage_2_valid;
assign motion_detector_enb = stage_2_valid;
assign memory_manager_enb  = stage_2_valid;
assign box_filter_enb      = stage_3_valid;
assign motion_overlay_enb  = stage_3_valid;

endmodule


