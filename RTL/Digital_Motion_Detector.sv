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
	input logic [31:0]				 s_axil_data, // {11bit width, 10bit height, 8bit threshold}
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
	
	logic handshake_ready;
	logic mp_enable;
	logic wr_background;
	logic [STREAM_WIDTH-1:0] highlighted_pixel;
	logic [STREAM_WIDTH-1:0] memory_pixel;
	logic [STREAM_WIDTH-1:0] data_delay;
	logic pixel_valid;
	logic pixel_last;
	
	assign handshake_ready = /*s_axis_tvalid &&*/ m_axis_tready && m_axi_awready && m_axi_wready && m_axi_arready && m_axi_rvalid;
	
	always_ff@(posedge clk or posedge rst) begin
		if(rst) begin
			memory_pixel <= '0;
		end else begin
			memory_pixel <= m_axi_rdata;
		end
	end
	
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
		  reg_width     <= s_axil_data[10:0];
		  reg_height    <= s_axil_data[21:11];
		  reg_threshold <= s_axil_data[29:22];
		  config_loaded <= 1'b1;
		end
	  end
	end

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
	.rbg_pixel    (s_axis_tdata),
	.memory_pixel (memory_pixel),
	.last_in_frame      (s_axis_tlast),
	.wr_background    (wr_background),
	.threshold	(reg_threshold),
	.width       (reg_width),
	.height (reg_height),
	.highlighted_pixel	(highlighted_pixel),
	.pixel_valid	(pixel_valid),
	.pixel_last (pixel_last)
  );

  //assign m_axis_tvalid = pixel_valid;
  assign m_axis_tdata = highlighted_pixel;
  assign m_axis_tlast = pixel_last;
  
  logic am_enable;



	// ---------------------------------------------------------------------------
	// Main FSM for Digital Motion Detector
	// ---------------------------------------------------------------------------
	// This FSM orchestrates the overall operation: waiting for config, processing
	// frames, and interacting with memory.
	typedef enum logic [1:0] {
	  IDLE,
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
	  // main pipeline
	  mp_enable = 0;
	  s_axis_tready = 0;
	  wr_background = 0;
	  m_axis_tvalid = 0;
	  // axi mem
	  am_enable = 0;
	  // ADDR
	  m_axi_awvalid = 0;
	  m_axi_arvalid = 0;
	  
	  //WRITE
	  m_axi_wvalid = 0;
	  m_axi_wdata = /*data_delay;*/s_axis_tdata;
	  //READ
	  m_axi_rready = 0;

	  case (current_state)
		IDLE: begin
		  if (config_loaded && handshake_ready) begin
			next_state = PROCESS_FIRST_FRAME;
			s_axis_tready = 1;
			if(s_axis_tvalid) begin
				// main pipeline
				mp_enable = 1;
				// axi mem
				am_enable = 1;
				// ADDR
				m_axi_awvalid = 1;
				m_axi_arvalid = 1;
				
				//WRITE
				m_axi_wvalid = 1;
				//READ
				m_axi_rready = 1;
			end
		  end else begin
			next_state = IDLE;
		  end
		end
		
		PROCESS_FIRST_FRAME: begin
			wr_background = 1;
			if(handshake_ready && s_axis_tvalid) begin
				// main pipeline
				mp_enable = 1;
				s_axis_tready = 1;
				// axi mem
				am_enable = 1;
				// ADDR
				m_axi_awvalid = 1;
				m_axi_arvalid = 1;
				
				//WRITE
				m_axi_wvalid = 1;
				//READ
				m_axi_rready = 1;
			end else if(handshake_ready && !s_axis_tvalid) begin
				s_axis_tready = 1;
			end
			if(s_axis_tlast && s_axis_tvalid) begin
				next_state = PROCESS_FRAME;
			end
		end

		PROCESS_FRAME: begin
		  if(handshake_ready && s_axis_tvalid) begin
			  // main pipeline
			  mp_enable = 1;
			  s_axis_tready = 1;
			  m_axis_tvalid = pixel_valid;
			  // axi mem
			  am_enable = 1;
			  // ADDR
			  m_axi_awvalid = 1;
			  m_axi_arvalid = 1;
			  
			  //WRITE
			  m_axi_wvalid = 1;
			  //READ
			  m_axi_rready = 1;
		  end else if(handshake_ready && !s_axis_tvalid) begin
			  s_axis_tready = 1;
		  end
		end

		default: begin
			next_state = IDLE;
		end
	  endcase
	end
	
	addr_manager am (
		.clk(clk),
		.rst(rst),
		.enable(am_enable),
		.last(s_axis_tlast),
		.write_addr(m_axi_awaddr),
		.read_addr(m_axi_araddr)
	);
	
	`ifndef SYNTHESIS
	`ifdef ENABLE_DMD_ASSERTIONS

	  // =========================================================================
	  // AXI4-Lite Slave (Configuration) Assertions
	  // =========================================================================

	  // as_axil_ready should be high whenever valid & not loaded
	  axil_ready_assert: assert property (
		@(posedge clk) disable iff (rst)
		(s_axil_valid && !config_loaded) |-> as_axil_ready
	  ) else $fatal("AXI4-Lite Slave not ready when it should be.");

	  // Configuration registers should update immediately when valid & not loaded
	  axil_config_update_assert: assert property (
			  @(posedge clk) disable iff (rst)
			  (s_axil_valid && !config_loaded) |=> 
				 (reg_width     == $past(s_axil_data[10:0]) &&
				  reg_height    == $past(s_axil_data[21:11]) &&
				  reg_threshold == $past(s_axil_data[29:22]))
			) else $fatal("AXI4-Lite Configuration registers did not update correctly.");


	  // config_loaded must go high right after valid config
	  config_loaded_set_assert: assert property (
		@(posedge clk) disable iff (rst)
		(s_axil_valid && !config_loaded) |=> config_loaded
	  ) else $fatal("config_loaded flag did not set after valid configuration.");

	  // Once config_loaded = 1, registers must remain stable
	  config_registers_stable_assert: assert property (
		@(posedge clk) disable iff (rst)
		(config_loaded) |=> 
		  ($stable(reg_width) && $stable(reg_height) && $stable(reg_threshold))
	  ) else $fatal("AXI4-Lite Configuration registers changed after config_loaded.");

	  // =========================================================================
	  // FSM State Transition Assertions
	  // =========================================================================

	  // IDLE -> PROCESS_FIRST_FRAME if config_loaded & handshake_ready
	  fsm_idle_to_first_frame_assert: assert property (
		@(posedge clk) disable iff (rst)
		(current_state == IDLE && config_loaded && handshake_ready) |=> 
		  (current_state == PROCESS_FIRST_FRAME)
	  ) else $fatal("FSM failed to transition from IDLE to PROCESS_FIRST_FRAME.");

	  // PROCESS_FIRST_FRAME PROCESS_FRAME on s_axis_tlast
	  fsm_first_frame_to_process_assert: assert property (
		@(posedge clk) disable iff (rst)
		(current_state == PROCESS_FIRST_FRAME && s_axis_tlast && s_axis_tvalid) |=> 
		  (current_state == PROCESS_FRAME)
	  ) else $fatal("FSM failed to transition PROCESS_FIRST_FRAME?PROCESS_FRAME.");

	  // =========================================================================
	  // AXI4-Stream Slave (Input Video)
	  // =========================================================================

	  // s_axis_tready must be high only in processing states
	  s_axis_tready_active_assert: assert property (
		@(posedge clk) disable iff (rst)
		((current_state inside {PROCESS_FIRST_FRAME, PROCESS_FRAME}) && handshake_ready) |-> s_axis_tready
	  ) else $fatal("s_axis_tready not active in processing state.");

	  // s_axis_tready must be low in IDLE
	  s_axis_tready_idle_assert: assert property (
			  @(posedge clk) disable iff (rst)
			  (current_state == IDLE && !config_loaded) |-> !s_axis_tready
			) else $fatal("s_axis_tready active in IDLE before config_loaded.");

	  // =========================================================================
	  // AXI4-Stream Master (Output Video)
	  // =========================================================================

	  // m_axis_tvalid must equal pixel_valid
	 /* m_axis_tvalid_follows_pixel_valid_assert: assert property (
		@(posedge clk) disable iff (rst)
		m_axis_tvalid == pixel_valid
	  ) else $fatal("m_axis_tvalid != pixel_valid.");*/

	  // m_axis_tdata == highlighted_pixel
	  always @(posedge clk) begin
		  if (m_axis_tvalid && m_axis_tready) begin
			if (m_axis_tdata !== highlighted_pixel) begin
			  #1ns; // wait a nanosecond for any combinational settle
			  if (m_axis_tdata !== highlighted_pixel)
				$fatal("m_axis_tdata != highlighted_pixel after settle");
			end
		  end
		end



	  // m_axis_tlast == pixel_last
	  m_axis_tlast_follows_pixel_last_assert: assert property (
			  @(posedge clk) disable iff (rst)
			  m_axis_tvalid |=> (m_axis_tlast == pixel_last)
			) else $fatal("m_axis_tlast != pixel_last while valid.");

	  // =========================================================================
	  // AXI4-Lite Master (Memory) Assertions
	  // =========================================================================

	  // Only active during processing states
	  axi_awvalid_active_assert: assert property (
		@(posedge clk) disable iff (rst)
		(current_state inside {PROCESS_FIRST_FRAME, PROCESS_FRAME} && handshake_ready && s_axis_tvalid) |-> m_axi_awvalid
	  ) else $fatal("m_axi_awvalid not asserted in processing.");

	  axi_wvalid_active_assert: assert property (
		@(posedge clk) disable iff (rst)
		(current_state inside {PROCESS_FIRST_FRAME, PROCESS_FRAME} && handshake_ready && s_axis_tvalid) |-> m_axi_wvalid
	  ) else $fatal("m_axi_wvalid not asserted in processing.");

	  axi_arvalid_active_assert: assert property (
		@(posedge clk) disable iff (rst)
		(current_state inside {PROCESS_FIRST_FRAME, PROCESS_FRAME} && handshake_ready && s_axis_tvalid) |-> m_axi_arvalid
	  ) else $fatal("m_axi_arvalid not asserted in processing.");

	  axi_rready_active_assert: assert property (
		@(posedge clk) disable iff (rst)
		(current_state inside {PROCESS_FIRST_FRAME, PROCESS_FRAME} && handshake_ready && s_axis_tvalid) |-> m_axi_rready
	  ) else $fatal("m_axi_rready not asserted in processing.");

	  axi_wdata_assignment_assert: assert property (
			  @(posedge clk) disable iff (rst)
			  (m_axi_wvalid && m_axi_wready) |-> (m_axi_wdata == s_axis_tdata)
			) else $fatal("m_axi_wdata != s_axis_tdata during valid write.");

	  // =========================================================================
	  // Internal Signals
	  // =========================================================================

	  // mp_enable high only in processing states
	  mp_enable_active_assert: assert property (
		@(posedge clk) disable iff (rst)
		(current_state inside {PROCESS_FIRST_FRAME, PROCESS_FRAME} && handshake_ready && s_axis_tvalid) |-> mp_enable
	  ) else $fatal("mp_enable inactive when expected.");

	  // wr_background only in PROCESS_FIRST_FRAME
	  wr_background_assert: assert property (
		@(posedge clk) disable iff (rst)
		wr_background == (current_state == PROCESS_FIRST_FRAME)
	  ) else $fatal("wr_background incorrect for state.");

	  // Reset check
	  reset_values_assert: assert property (
		@(posedge clk)
		rst |-> (current_state == IDLE &&
				 reg_width     == '0 &&
				 reg_height    == '0 &&
				 reg_threshold == '0 &&
				 config_loaded == 1'b0 &&
				 memory_pixel  == '0)
	  ) else $fatal("Module did not reset correctly.");

	`endif
	`endif




  endmodule
