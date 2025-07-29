/*------------------------------------------------------------------------------
 * File          : dmd_tb.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jun 11, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module dmd_tb;
import uvm_pkg::*;
`include "uvm_macros.svh"

dmd_if vif();

Digital_Motion_Detector dut (
	.clk              (vif.clk),
	.rst              (vif.rst),
	// AXI4-Stream Slave (input video)
	.s_axis_tvalid    (vif.s_axis_tvalid),
	.s_axis_tready    (vif.s_axis_tready),
	.s_axis_tdata     (vif.s_axis_tdata),
	.s_axis_tlast     (vif.s_axis_tlast),
	// AXI4-Stream Master (output video)
	.m_axis_tvalid    (vif.m_axis_tvalid),
	.m_axis_tready    (vif.m_axis_tready),
	.m_axis_tdata     (vif.m_axis_tdata),
	.m_axis_tlast     (vif.m_axis_tlast),
	// AXI4-Lite Slave (config: width/height/threshold) - Direct connections
	.s_axil_valid     (vif.s_axil_valid),
	.s_axil_data     (vif.s_axil_data),
	.as_axil_ready    (vif.as_axil_ready),
	// AXI4-Lite Master (memory for pixels)
	.m_axi_awvalid    (vif.m_axi_awvalid),
	.m_axi_awready    (vif.m_axi_awready),
	.m_axi_awaddr     (vif.m_axi_awaddr),
	.m_axi_wvalid     (vif.m_axi_wvalid),
	.m_axi_wready     (vif.m_axi_wready),
	.m_axi_wdata      (vif.m_axi_wdata),
	.m_axi_arvalid    (vif.m_axi_arvalid),
	.m_axi_arready    (vif.m_axi_arready),
	.m_axi_araddr     (vif.m_axi_araddr),
	.m_axi_rvalid     (vif.m_axi_rvalid),
	.m_axi_rready     (vif.m_axi_rready),
	.m_axi_rdata      (vif.m_axi_rdata)
);

// Generate 30 MHz clock: period = 33.333 ns
initial begin
  vif.clk = 0;
  forever #(33.333/2) vif.clk = ~vif.clk;
end

initial begin
  vif.rst = 1;
  #100;
  vif.rst = 0;
end

localparam ADDR_WIDTH  = 32;
localparam DATA_WIDTH  = 32;
localparam MEM_WIDTH_PIXELS  = 1280;
localparam MEM_HEIGHT_PIXELS = 720;
localparam MEM_SIZE          = MEM_WIDTH_PIXELS * MEM_HEIGHT_PIXELS*4; // Number of 32-bit words
logic [DATA_WIDTH-1:0] memory [MEM_SIZE-1:0];
localparam int BASE_ADDR        = 32'h0000_0000;
localparam int FRAME_SIZE_BYTES = 3_686_400;
localparam int TOTAL_MEM_SIZE   = 4 * FRAME_SIZE_BYTES;

// Internal state for AXI-Lite slave handshakes
logic aw_hs, w_hs, ar_hs, r_hs;
logic [ADDR_WIDTH-1:0] aw_addr_q, ar_addr_q; // Queued addresses

// AXI Write Address Channel (AW)
always_ff @(posedge vif.clk or posedge vif.rst) begin
	if (vif.rst) begin
		aw_addr_q <= 0;
	end else begin
		if (vif.m_axi_awvalid && vif.m_axi_awready) begin
			aw_addr_q <= vif.m_axi_awaddr; // Latch address on handshake
		end
	end
end

// AXI Write Data Channel (W)
always_ff @(posedge vif.clk or posedge vif.rst) begin
	if (vif.rst) begin
	end else begin
		if (vif.m_axi_wvalid && vif.m_axi_wready) begin
			memory[aw_addr_q / (DATA_WIDTH/8)] <= vif.m_axi_wdata;
		end
	end
end

// AXI Read Address Channel (AR)
always_ff @(posedge vif.clk or posedge vif.rst) begin
	if (vif.rst) begin
		ar_addr_q <= 0;
	end else begin
		if (vif.m_axi_arvalid && vif.m_axi_arready) begin
			ar_addr_q <= vif.m_axi_araddr; // Latch address on handshake
		end
	end
end

// AXI Read Data Channel (R)
logic [DATA_WIDTH-1:0] rdata_reg;
always_ff @(posedge vif.clk or posedge vif.rst) begin
	if (vif.rst) begin
		rdata_reg <= 0;
	end else begin
		// If read address handshake occurred, prepare data for next cycle
		if (vif.m_axi_arvalid && vif.m_axi_arready) begin
			rdata_reg <= memory[ar_addr_q / (DATA_WIDTH/8)];
		end
	end
end
assign vif.m_axi_rdata = rdata_reg; // Drive rdata from register

covergroup dmd_coverage @(posedge vif.clk);

	// Cover FSM states
	fsm_state_cp: coverpoint dut.current_state iff (!vif.rst) {
	  bins IDLE_b                  = {dut.IDLE};
	  bins PROCESS_FIRST_FRAME_b   = {dut.PROCESS_FIRST_FRAME};
	  bins PROCESS_FRAME_b         = {dut.PROCESS_FRAME};
	}

	// Cover AXI4-Lite Configuration Width (sample only when not in reset)
	config_width_cp: coverpoint dut.reg_width iff (!vif.rst) {
	  bins typical_width  = {[255:1279]};   // Typical range
	  //bins max_width      = {1280};
	  ignore_bins zero_val = {0};           // Always ignore 0 in functional cases
	}

	// Cover AXI4-Lite Configuration Height
	config_height_cp: coverpoint dut.reg_height iff (!vif.rst) {
	  bins typical_height  = {[255:719]};
	  //bins max_height      = {720};
	  ignore_bins zero_val = {0};
	}

	// Cover config_loaded status
	config_loaded_cp: coverpoint dut.config_loaded iff (!vif.rst) {
	  bins loaded     = {1};
	  bins not_loaded = {0};
	}

	// Cross coverage for config_loaded and FSM states
	config_fsm_cross: cross fsm_state_cp, config_loaded_cp {
	  // Ignore impossible/illegal combos
	  ignore_bins idle_loaded = binsof(fsm_state_cp) intersect {dut.IDLE} &&
								binsof(config_loaded_cp) intersect {1};

	  ignore_bins process_not_loaded = binsof(fsm_state_cp) intersect 
									   {dut.PROCESS_FIRST_FRAME, dut.PROCESS_FRAME} &&
									   binsof(config_loaded_cp) intersect {0};
	}
	
	fsm_transition_cp: coverpoint dut.current_state iff (!vif.rst) {
		bins idle_to_first   = (dut.IDLE => dut.PROCESS_FIRST_FRAME);
		bins first_to_frame  = (dut.PROCESS_FIRST_FRAME => dut.PROCESS_FRAME);
	}
	
	s_axis_tlast_cp: coverpoint vif.s_axis_tlast iff (!vif.rst) {
		bins last_seen = {1};
		bins no_last   = {0};
	  }
	
	frame_boundary_cross: cross s_axis_tlast_cp, fsm_state_cp {
		// Exclude combinations where the FSM state is IDLE
		ignore_bins idle_state = binsof(fsm_state_cp) intersect {dut.IDLE};
	  }

	config_reload_attempt_cp: coverpoint (vif.s_axil_valid && dut.config_loaded) iff (!vif.rst) {
		bins reload_attempt = {1};
	  }

	// AXI4-Stream Slave (Input) Handshake
	s_axis_handshake_cp: coverpoint {vif.s_axis_tvalid, vif.s_axis_tready} iff (!vif.rst) {
	  bins valid_ready        = {2'b11};
	  bins valid_not_ready    = {2'b10};
	  bins not_valid_ready    = {2'b01};
	  bins not_valid_not_ready= {2'b00};
	}

	// AXI4-Stream Master (Output) Handshake
	m_axis_handshake_cp: coverpoint {vif.m_axis_tvalid, vif.m_axis_tready} iff (!vif.rst) {
	  bins valid_ready        = {2'b11};
	  //bins valid_not_ready    = {2'b10};
	  bins not_valid_ready    = {2'b01};
	  bins not_valid_not_ready= {2'b00};
	}

	// Cross coverage for input/output stream handshakes
	stream_handshake_cross: cross s_axis_handshake_cp, m_axis_handshake_cp {
		// Both streams are transferring data
		bins input_output_transfer = binsof(s_axis_handshake_cp.valid_ready) &&
									 binsof(m_axis_handshake_cp.valid_ready);
		// Input is stalled (valid, not ready), Output is transferring
		//bins input_stall_output_transfer = binsof(s_axis_handshake_cp.valid_not_ready) &&
			//							   binsof(m_axis_handshake_cp.valid_ready);
		// Input is transferring, Output is stalled (valid, not ready)
		/*bins input_transfer_output_stall = binsof(s_axis_handshake_cp.valid_ready) &&
										   binsof(m_axis_handshake_cp.valid_not_ready);*/
		// Both streams are stalled (valid, not ready)
		/*bins both_stalled = binsof(s_axis_handshake_cp.valid_not_ready) &&
							binsof(m_axis_handshake_cp.valid_not_ready);*/
		// Both streams are idle (not valid, not ready)
		bins both_idle = binsof(s_axis_handshake_cp.not_valid_not_ready) &&
						 binsof(m_axis_handshake_cp.not_valid_not_ready);

	//	illegal_bins ILLEGAL_S_NVNR_M_NVNR = binsof(s_axis_handshake_cp.not_valid_not_ready) &&
		//									 binsof(m_axis_handshake_cp.not_valid_not_ready);

		//illegal_bins ILLEGAL_S_NVNR_M_VALID_ANY_READY = binsof(s_axis_handshake_cp.not_valid_not_ready) &&
			//											(binsof(m_axis_handshake_cp.valid_not_ready) || binsof(m_axis_handshake_cp.valid_ready));

		ignore_bins ILLEGAL_S_VR_M_NVNR = binsof(s_axis_handshake_cp.valid_ready) &&
								   binsof(m_axis_handshake_cp.not_valid_not_ready);
		
		ignore_bins no_input_but_output_transfer = 
				binsof(s_axis_handshake_cp.not_valid_not_ready) &&
				binsof(m_axis_handshake_cp.valid_ready);

			  ignore_bins input_not_valid_output_idle = 
				binsof(s_axis_handshake_cp.not_valid_ready) &&
				binsof(m_axis_handshake_cp.not_valid_not_ready);

			  ignore_bins input_not_valid_output_transfer = 
				binsof(s_axis_handshake_cp.not_valid_ready) &&
				binsof(m_axis_handshake_cp.valid_ready);
			  
			  ignore_bins input_stall_output_transfer = 
					  binsof(s_axis_handshake_cp.valid_not_ready) &&
					  binsof(m_axis_handshake_cp.valid_ready);

	//	ignore_bins ILLEGAL_S_VR_M_VNR = binsof(s_axis_handshake_cp.valid_ready) &&
		//								  binsof(m_axis_handshake_cp.valid_not_ready);

	  }

	// AXI4-Lite Master (Memory) Write Address Handshake
	m_axi_aw_handshake_cp: coverpoint {vif.m_axi_awvalid, vif.m_axi_awready} iff (!vif.rst) {
	  bins valid_ready        = {2'b11};
	  //bins valid_not_ready    = {2'b10};
	  bins not_valid_ready    = {2'b01};
	  bins not_valid_not_ready= {2'b00};
	}

	// AXI4-Lite Master (Memory) Write Data Handshake
	m_axi_w_handshake_cp: coverpoint {vif.m_axi_wvalid, vif.m_axi_wready} iff (!vif.rst) {
	  bins valid_ready        = {2'b11};
	  //bins valid_not_ready    = {2'b10};
	  bins not_valid_ready    = {2'b01};
	  bins not_valid_not_ready= {2'b00};
	}

	// AXI4-Lite Master (Memory) Read Address Handshake
	m_axi_ar_handshake_cp: coverpoint {vif.m_axi_arvalid, vif.m_axi_arready} iff (!vif.rst) {
	  bins valid_ready        = {2'b11};
	  //bins valid_not_ready    = {2'b10};
	  bins not_valid_ready    = {2'b01};
	  bins not_valid_not_ready= {2'b00};
	}

	// AXI4-Lite Master (Memory) Read Data Handshake
	m_axi_r_handshake_cp: coverpoint {vif.m_axi_rvalid, vif.m_axi_rready} iff (!vif.rst) {
	  bins valid_ready        = {2'b11};
	  bins valid_not_ready    = {2'b10};
	  //bins not_valid_ready    = {2'b01};
	  bins not_valid_not_ready= {2'b00};
	}

	// Separate coverpoints for mp_enable & wr_background (no inline coverpoint in cross!)
	mp_enable_cp: coverpoint dut.mp_enable iff (!vif.rst) {
	  bins enabled  = {1};
	  bins disabled = {0};
	}

	wr_background_cp: coverpoint dut.wr_background iff (!vif.rst) {
	  bins enabled  = {1};
	  bins disabled = {0};
	}

	// Cross coverage for FSM state vs mp_enable
	mp_enable_fsm_cross: cross fsm_state_cp, mp_enable_cp {
		ignore_bins mp_enable_in_idle = binsof(fsm_state_cp) intersect {dut.IDLE} &&
										binsof(mp_enable_cp) intersect {1};
	  }

	// Cover handshake_ready signal
	handshake_ready_cp: coverpoint dut.handshake_ready iff (!vif.rst) {
	  bins ready     = {1};
	  bins not_ready = {0};
	}

	// Define the covergroup for AXI address coverage
	  // Coverpoint for AXI Write Addresses
	  axi_awaddr_cp: coverpoint vif.m_axi_awaddr iff (!vif.rst && vif.m_axi_awvalid && vif.m_axi_awready) {
		bins start_addr    = {BASE_ADDR};
		bins quarter       = {[BASE_ADDR + 1 : BASE_ADDR + TOTAL_MEM_SIZE/4]};
		bins half          = {[BASE_ADDR + TOTAL_MEM_SIZE/4 + 1 : BASE_ADDR + TOTAL_MEM_SIZE/2]};
		bins three_quart   = {[BASE_ADDR + TOTAL_MEM_SIZE/2 + 1 : BASE_ADDR + (3*TOTAL_MEM_SIZE)/4]};
		bins end_addr      = {[BASE_ADDR + (3*TOTAL_MEM_SIZE)/4 + 1 : BASE_ADDR + TOTAL_MEM_SIZE - (DATA_WIDTH/8)]};
	  }

	  // Coverpoint for AXI Read Addresses (identical structure to write addresses)
	  axi_araddr_cp: coverpoint vif.m_axi_araddr iff (!vif.rst && vif.m_axi_arvalid && vif.m_axi_arready) {
		bins start_addr    = {BASE_ADDR};
		bins quarter       = {[BASE_ADDR + 1 : BASE_ADDR + TOTAL_MEM_SIZE/4]};
		bins half          = {[BASE_ADDR + TOTAL_MEM_SIZE/4 + 1 : BASE_ADDR + TOTAL_MEM_SIZE/2]};
		bins three_quart   = {[BASE_ADDR + TOTAL_MEM_SIZE/2 + 1 : BASE_ADDR + (3*TOTAL_MEM_SIZE)/4]};
		bins end_addr      = {[BASE_ADDR + (3*TOTAL_MEM_SIZE)/4 + 1 : BASE_ADDR + TOTAL_MEM_SIZE - (DATA_WIDTH/8)]};
	  }

	// Cross AXI Read/Write addresses with s_axis_tlast to ensure address resets/wraps at frame boundaries
	axi_addr_tlast_cross: cross axi_awaddr_cp, s_axis_tlast_cp {		
		ignore_bins ignore_start_awaddr = 
		  binsof(axi_awaddr_cp.start_addr);
	  }

	  axi_addr_tlast_cross_read: cross axi_araddr_cp, s_axis_tlast_cp {
		ignore_bins ignore_start_araddr = 
		  binsof(axi_araddr_cp.start_addr);
	  }

	
	highlighted_pixel_cp: coverpoint dut.highlighted_pixel iff (!vif.rst && dut.pixel_valid) {
		bins highlight_color = {dut.HIGHLIGHT_COLOR};
		bins non_highlight_color = default; // Any other color
		//bins zero_val = {0};
	}
	
	m_axi_wdata_cp: coverpoint vif.m_axi_wdata iff (!vif.rst && vif.m_axi_wvalid && vif.m_axi_wready) {
		bins first_quarter  = {[32'h0000_0000 : 32'h3FFF_FFFF]};
		bins second_quarter = {[32'h4000_0000 : 32'h7FFF_FFFF]};
		bins third_quarter  = {[32'h8000_0000 : 32'hBFFF_FFFF]};
		bins fourth_quarter = {[32'hC000_0000 : 32'hFFFF_FFFF]};
	  }

	m_axi_rdata_cp: coverpoint vif.m_axi_rdata iff (!vif.rst && vif.m_axi_rvalid && vif.m_axi_rready) {
		bins first_quarter  = {[32'h0000_0000 : 32'h3FFF_FFFF]};
		bins second_quarter = {[32'h4000_0000 : 32'h7FFF_FFFF]};
		bins third_quarter  = {[32'h8000_0000 : 32'hBFFF_FFFF]};
		bins fourth_quarter = {[32'hC000_0000 : 32'hFFFF_FFFF]};
	  }

  endgroup


initial begin
	// Create an instance of the covergroup
	dmd_coverage dmd_cg = new();
end

// UVM configuration and run
initial begin
  uvm_config_db#(virtual dmd_if)::set(null, "*", "vif", vif);
  run_test("dmd_test");
end

endmodule
