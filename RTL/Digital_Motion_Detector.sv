/*------------------------------------------------------------------------------
 * File          : Digital_Motion_Detector.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jul 4, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module Digital_Motion_Detector #(
	parameter int WIDTH_BITS       = 11,
	parameter int HEIGHT_BITS      = 10,
	parameter int LABEL_WIDTH      = 8,
	parameter int NUM_LABELS       = 1 << LABEL_WIDTH,
	parameter int MAX_WIDTH        = 1 << WIDTH_BITS,
	parameter logic [31:0] HIGHLIGHT_COLOR = 32'hFF000000,
	parameter STREAM_WIDTH    = 32, // AXI4-Stream data width
	parameter ADDR_WIDTH      = 32, // AXI4-Lite Master address width
	parameter DATA_WIDTH      = 32  // AXI4-Lite Master data width (should match STREAM_WIDTH for pixels)
  )(
	input  logic                     clk,
	input  logic                     rst,

	// AXI4-Stream Slave (input video)
	input  logic                     s_axis_tvalid,
	output logic                     s_axis_tready,
	input  logic [STREAM_WIDTH-1:0]  s_axis_tdata,
	input  logic                     s_axis_tlast,

	// AXI4-Stream Master (output video)
	output logic                     m_axis_tvalid,
	input  logic                     m_axis_tready,
	output logic [STREAM_WIDTH-1:0]  m_axis_tdata,
	output logic                     m_axis_tlast,

	// AXI4-Lite Slave (config: width/height/threshold)
	input  logic                     s_axil_valid,
	input  logic [10:0]              s_axil_width,
	input  logic [9:0]               s_axil_height,
	input  logic [7:0]               s_axil_threshold,
	output logic                     as_axil_ready, // AXI-Lite Slave Ready

	// AXI4-Lite Master (memory for pixels)
	// Write Address Channel
	output logic                     m_axi_awvalid,
	input  logic                     m_axi_awready,
	output logic [ADDR_WIDTH-1:0]    m_axi_awaddr,
	// Write Data Channel
	output logic                     m_axi_wvalid,
	input  logic                     m_axi_wready,
	output logic [DATA_WIDTH-1:0]    m_axi_wdata,

	// Read Address Channel
	output logic                     m_axi_arvalid,
	input  logic                     m_axi_arready,
	output logic [ADDR_WIDTH-1:0]    m_axi_araddr,
	// Read Data Channel
	input  logic                     m_axi_rvalid,
	output logic                     m_axi_rready,
	input  logic [DATA_WIDTH-1:0]    m_axi_rdata
  );

  // Configuration Registers (read from AXI4-Lite Slave)
	logic [10:0]  reg_width;
	logic [9:0]   reg_height;
	logic [7:0]   reg_threshold;
	logic         config_loaded; // Flag to indicate if configuration is loaded
	
	logic memory_error;
	logic mp_enable;
	logic wr_background;
	logic [STREAM_WIDTH-1:0] highlighted_pixel;
	logic [STREAM_WIDTH-1:0] memory_pixel [1:0];
	logic pixel_valid;
	logic pixel_last;

  motion_pipeline #(
		 .WIDTH_BITS(WIDTH_BITS),
		.HEIGHT_BITS(HEIGHT_BITS),
		.LABEL_WIDTH(LABEL_WIDTH),
		.NUM_LABELS(NUM_LABELS),
		.MAX_WIDTH(MAX_WIDTH),
		.HIGHLIGHT_COLOR(HIGHLIGHT_COLOR))
  	mp(
	.clk             (clk),
	.rst             (rst),
	.enable          (mp_enable),
	.rgb_pixel    (s_axis_tdata),
	.memory_pixel (memory_pixel[1]),
	.last_in_frame      (s_axis_tlast),
	.wr_background    (wr_background),
	.threshold	(reg_threshold),
	.width       (reg_width),
	.height (reg_height),
	.highlighted_pixel	(highlighted_pixel),
	.pixel_valid	(pixel_valid),
	.pixel_last (pixel_last)
  );

  assign m_axis_tvalid = pixel_valid;
  assign m_axis_tdata = highlighted_pixel;
  assign m_axis_tlast = pixel_last;

	// ---------------------------------------------------------------------------
	// AXI4-Lite Slave (Configuration) Logic
	// ---------------------------------------------------------------------------
	// This block handles receiving configuration parameters (width, height, threshold)
	// from an AXI4-Lite master.

	assign as_axil_ready = s_axil_valid && !config_loaded; // Ready to accept config if valid and not yet loaded

	always_ff @(posedge clk or posedge rst) begin
	  if (rst) begin
		reg_width     <= '0;
		reg_height    <= '0;
		reg_threshold <= '0;
		config_loaded <= 1'b0;
	  end else begin
		if (s_axil_valid && !config_loaded) begin // Only load once
		  reg_width     <= s_axil_width;
		  reg_height    <= s_axil_height;
		  reg_threshold <= s_axil_threshold;
		  config_loaded <= 1'b1;
		end
	  end
	end

	// ---------------------------------------------------------------------------
	// Main FSM for Digital Motion Detector
	// ---------------------------------------------------------------------------
	// This FSM orchestrates the overall operation: waiting for config, processing
	// frames, and interacting with memory.
	typedef enum logic [1:0] {
	  IDLE,
	  READY_TO_PROCESS_FRAME,
	  PROCESS_FIRST_FRAME,
	  PROCESS_FRAME
	} fsm_state_t;

	fsm_state_t current_state, next_state;

	always_ff @(posedge clk or posedge rst) begin
	  if (rst) begin
		current_state <= IDLE;
	  end else begin
		current_state <= next_state;
	  end
	end

	always_comb begin
	  next_state = current_state; // Default to staying in current state
	  mp_enable = 0;
	  s_axis_tready = 0;
	  wr_background = 0;

	  case (current_state)
		IDLE: begin
		  if (config_loaded && m_axis_tready) begin
			next_state = READY_TO_PROCESS_FRAME;
		  end else begin
			next_state = IDLE;
		  end
		end

		READY_TO_PROCESS_FRAME: begin
		  s_axis_tready = 1'b1;
		  if(!m_axis_tready || memory_error) begin
			  next_state = IDLE;
		  end else if(s_axis_tvalid) begin
			  mp_enable = 1;
			  next_state = PROCESS_FIRST_FRAME;
			  wr_background = 1;
		  end
		end
		
		PROCESS_FIRST_FRAME: begin
			mp_enable = 1;
			wr_background = 1;
			s_axis_tready = 1'b1;
			if(!s_axis_tvalid || !m_axis_tready || memory_error) begin
				next_state = IDLE;
			end else if(s_axis_tlast) begin
				next_state = PROCESS_FRAME;
			end
		end

		PROCESS_FRAME: begin
		  mp_enable = 1;
		  s_axis_tready = 1'b1;
		  if(!s_axis_tvalid || !m_axis_tready || memory_error) begin
			  next_state = IDLE;
		  end
		end

		default: begin
			next_state = IDLE;
		end
	  endcase
	end

	// ---------------------------------------------------------------------------
	// AXI4-Lite Master (Memory Access) Logic
	// ---------------------------------------------------------------------------
	logic am_enable;
	addr_manager am (
		.clk(clk),
		.rst(rst),
		.enable(am_enable),
		.write_addr(m_axi_awaddr),
		.read_addr(m_axi_araddr)
	);
	// ADRESS
	always_ff@(posedge clk or posedge rst) begin
		if(rst) begin
			m_axi_awvalid <= 0;
			m_axi_arvalid <= 0;
			am_enable <= 0;
		end else begin
			m_axi_awvalid <= m_axi_awready
					&& (current_state == PROCESS_FIRST_FRAME
						|| current_state == PROCESS_FRAME);
			m_axi_arvalid <= m_axi_arready
					&& (current_state == PROCESS_FIRST_FRAME
						|| current_state == PROCESS_FRAME);
			am_enable <= !memory_error
					&& (current_state == PROCESS_FIRST_FRAME
						|| current_state == PROCESS_FRAME);
		end
	end
	
	// DATA
	always_ff@(posedge clk or posedge rst) begin
		if(rst) begin
			m_axi_wvalid <= 0;
			m_axi_wdata <= '0;
			memory_pixel[0] <= '0;
			memory_pixel[1] <= '0;
		end else begin
			// WRITE DATA
			if((current_state == PROCESS_FIRST_FRAME || current_state == PROCESS_FRAME)
				&& 	m_axi_wready) begin
				m_axi_wvalid <= 1;
				m_axi_wdata <= s_axis_tdata;
			end else begin
				m_axi_wvalid <= 0;
				m_axi_wdata <= '0;
			end
			// READ DATA
			if((current_state == PROCESS_FIRST_FRAME || current_state == PROCESS_FRAME)
					&& 	m_axi_rvalid) begin
					m_axi_rready <= 1;
					memory_pixel[0] <= m_axi_rdata;
					memory_pixel[1] <= memory_pixel[0];
				end else begin
					m_axi_rready <= 0;
					memory_pixel[0] <= '0;
					memory_pixel[1] <= '0;
				end
		end
	end
	
	always_comb begin
		memory_error = 0; // Default to no error
		if ((current_state == PROCESS_FIRST_FRAME
			  || current_state == PROCESS_FRAME)
			&& (!m_axi_awready   // If memory not ready for write address
				|| !m_axi_wready   // OR memory not ready for write data
				|| !m_axi_arready)) // OR memory not ready for read address
		  memory_error = 1; // Assert error
	  end

  endmodule
