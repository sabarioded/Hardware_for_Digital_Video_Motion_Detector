/*------------------------------------------------------------------------------
 * File          : control.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 10, 2025
 * Description   : Pipelined control FSM with AXI4-Stream, AXI4-Lite, and stage control
 *------------------------------------------------------------------------------*/

module control (
	input  logic        clk,
	input  logic        rst,

	// AXI Stream handshake
	input  logic        input_valid,
	input  logic        output_ready,
	output logic        axi_stream_valid,
	output logic        axi_stream_ready,

	// AXI-Lite handshake (for config)
	output logic        axi_lite_ready,

	// AXI Stream input frame end marker
	input  logic        last,

	// Enables for pipeline stages
	output logic        frame_manager_enb,
	output logic        sigma_delta_enb,
	output logic        motion_detector_enb,
	output logic        map_manager_enb,   // enable motion_map_manager

	// Control signals
	output logic        wr_background,
	output logic        rotate
);

	//----------------------------------------------------------------------
	// Handshake & activity indicator
	//----------------------------------------------------------------------
	logic running;
	logic active;
	assign active = input_valid && output_ready;

	// AXI-Lite ready when not actively streaming
	assign axi_lite_ready   = !active;

	// Rotate pulse at end-of-frame when streaming
	assign rotate           = active && last;

	//----------------------------------------------------------------------
	// FSM states
	//----------------------------------------------------------------------
	typedef enum logic [1:0] { IDLE = 2'd0, SETUP = 2'd1, RUN = 2'd2 } state_t;
	state_t PS, NS;
	
	// Drive AXI-Stream ready/valid
	assign axi_stream_ready = active;
	assign axi_stream_valid = running && active;

	always_ff @(posedge clk or posedge rst) begin
		if (rst)
			PS <= IDLE;
		else
			PS <= NS;
	end

	always_comb begin
		// Default assignments
		NS                   = PS;
		frame_manager_enb    = 1'b0;
		sigma_delta_enb      = 1'b0;
		motion_detector_enb  = 1'b0;
		map_manager_enb      = 1'b0;
		wr_background        = 1'b0;
		running = 1'b0;

		case (PS)
			IDLE: begin
				running = 1'b0;
				if (active)
					NS = SETUP;
			end

			SETUP: begin
				// Initialize background and stream first pixel
				frame_manager_enb   = 1'b1;
				sigma_delta_enb     = 1'b1;
				wr_background       = 1'b1;
				if (!active)
					NS = IDLE;
				else if (last)
					NS = RUN;
			end

			RUN: begin
				// Full pipeline after setup
				running = 1'b1;
				wr_background = 1'b0;
				frame_manager_enb    = 1'b1;
				sigma_delta_enb      = 1'b1;
				motion_detector_enb  = 1'b1;
				map_manager_enb      = 1'b1;
				if (!active)
					NS = IDLE;
			end

			default: NS = PS;
		endcase
	end

endmodule
