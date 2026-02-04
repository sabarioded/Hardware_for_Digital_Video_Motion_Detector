/*------------------------------------------------------------------------------
 * File        : dmd_scoreboard.sv
 * Project     : Project_RTL
 * Author      : eposmk
 * Creation date : Jul 28, 2025
 * Description :
 * UVM scoreboard for Digital Motion Detector with relaxed checks for
 * constrained-random testing (stalls, mid-run reloads, random frame sizes).
 *------------------------------------------------------------------------------*/

class dmd_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(dmd_scoreboard)

  // Analysis port from the dmd_monitor
  uvm_analysis_imp#(dmd_trans, dmd_scoreboard) ap;

  // Maximum expected buffer size (large enough for any config)
  localparam int TB_WIDTH_BITS       = 11; // Max 2048 pixels wide
  localparam int TB_HEIGHT_BITS      = 10; // Max 1024 lines
  localparam int TB_STREAM_WIDTH     = 32; // Assuming 32-bit pixel data (ARGB)
  localparam int MAX_REF_WIDTH       = (1 << TB_WIDTH_BITS);
  localparam int MAX_REF_HEIGHT      = (1 << TB_HEIGHT_BITS);
  localparam int MAX_FRAME_SIZE      = MAX_REF_WIDTH * MAX_REF_HEIGHT;

  // Internal DUT configuration (captured dynamically)
  logic [10:0]  configured_width;
  logic [9:0]   configured_height;
  logic [7:0]   configured_threshold; // Added to track threshold
  logic         config_loaded;           // Flag to indicate if configuration is loaded
  int unsigned  current_frame_size;      // computed width * height

  // Pixel counters for current frame processing
  int unsigned current_x;
  int unsigned current_y;
  int unsigned current_frame_id;
  logic any_handshake_high;
  logic all_handshake_high;
  logic handshake_ready;
  logic handshake_input;
  logic handshake_output;

  // Buffer to store the DUT's output pixels for the current frame
  logic [TB_STREAM_WIDTH-1:0] output_pixel_dut [0:MAX_FRAME_SIZE-1];

  // File dumping variables
  string dump_name;
  int    dump_fd;

  function new(string name, uvm_component parent = null);
	super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	ap = new("ap", this);

	// Initialize scoreboard state
	configured_width      = '0;
	configured_height     = '0;
	configured_threshold  = '0; // Initialize threshold
	config_loaded         = 0;
	current_frame_size    = 0;
	current_x             = 0;
	current_y             = 0;
	current_frame_id      = 0;

	// Clear DUT output buffer
	foreach (output_pixel_dut[i]) output_pixel_dut[i] = '0;
  endfunction

  //----------------------------------------------------------------------------
  // write() function - called for every transaction from monitor
  //----------------------------------------------------------------------------
  virtual function void write(dmd_trans tr);

	//--------------------------------------------------------------------
	// 1. Handle AXI-Lite Config Transactions
	//--------------------------------------------------------------------
	if (tr.s_axil_valid && tr.as_axil_ready) begin
	  logic [10:0]  new_width    = tr.s_axil_data[10:0];
	  logic [9:0]   new_height   = tr.s_axil_data[21:11];
	  logic [7:0]   new_threshold = tr.s_axil_data[29:22];

	  if (!config_loaded) begin
		// Initial configuration load
		configured_width    = new_width;
		configured_height   = new_height;
		configured_threshold = new_threshold;
		current_frame_size  = configured_width * configured_height;
		config_loaded = 1'b1;

		`uvm_info("DMD_SCB",
		  $sformatf("Initial config loaded: WxH=%0dx%0d, Threshold=%0d, FrameSize=%0d",
					configured_width, configured_height, configured_threshold, current_frame_size),
		  UVM_HIGH)

	  end
	 end

	//--------------------------------------------------------------------
	// 2. Check for handshake activity before configuration is loaded
	//--------------------------------------------------------------------
	if (!config_loaded) begin
	  if(tr.m_axis_tvalid || tr.s_axis_tready || tr.m_axi_awvalid || tr.m_axi_wvalid || tr.m_axi_arvalid || tr.m_axi_rready) begin
		`uvm_error("DMD_SCB",
		  $sformatf("DUT asserted handshake signal(s) before configuration was loaded! "));
		return; // Stop processing this transaction as it's an invalid state
	  end
	end
	handshake_ready = tr.s_axis_tvalid && tr.m_axis_tready && tr.m_axi_awready && tr.m_axi_wready && tr.m_axi_arready && tr.m_axi_rvalid;
	//--------------------------------------------------------------------
	// 3. Check for handshake signal consistency after config is loaded
	//--------------------------------------------------------------------
	if (config_loaded ) begin
	  any_handshake_high = tr.m_axi_awvalid || tr.m_axi_wvalid || tr.m_axi_arvalid || tr.m_axi_rready;
	  all_handshake_high = tr.m_axi_awvalid && tr.m_axi_wvalid && tr.m_axi_arvalid && tr.m_axi_rready;
	  handshake_input = tr.s_axis_tvalid && tr.s_axis_tready;
	  handshake_output = tr.m_axis_tvalid && tr.m_axis_tready;
	  
	  if(handshake_ready && !all_handshake_high) begin
		  `uvm_error("DMD_SCB",
				  $sformatf("Handshake ready but not all signals high "));
	  end

	  // Error if some are high and some are low (i.e., not all high AND not all low)
	  if (any_handshake_high && !all_handshake_high) begin
		`uvm_error("DMD_SCB",
		  $sformatf("Inconsistent handshake signals detected after configuration! Expected all high or all low. "));
	  end
	  
	  if ((!handshake_input && handshake_output) || (handshake_input && !tr.m_axis_tready)) begin
		  `uvm_error("DMD_SCB", $sformatf("handshake input and handshake output not active together - s_axis_tvalid=%b, s_axis_tready=%b, m_axis_tvalid=%b, m_axis_tready=%b", tr.s_axis_tvalid, tr.s_axis_tready, tr.m_axis_tvalid, tr.m_axis_tready));
		end
	end

	//--------------------------------------------------------------------
	// 4. Process DUT Output Pixels (Only when valid handshake)
	//--------------------------------------------------------------------
	if (!config_loaded && tr.m_axis_tvalid && tr.m_axis_tready) begin
	  `uvm_error("DMD_SCB",
		$sformatf("DUT outputting pixels (m_axis_tvalid & m_axis_tready) before configuration is loaded! Current frame ID: %0d", current_frame_id));
	  return; // Do not process this pixel further, as configuration is invalid
	end

	if (tr.m_axis_tvalid && tr.m_axis_tready) begin
	  int pixel_idx = current_y * configured_width + current_x;

	  if (pixel_idx < MAX_FRAME_SIZE) begin
		output_pixel_dut[pixel_idx] = tr.m_axis_tdata;
	  end else begin
		`uvm_error("DMD_SCB",
		  $sformatf("Pixel index %0d exceeds MAX_FRAME_SIZE=%0d (WxH=%0dx%0d) for frame %0d. This indicates an issue with frame size calculation or unexpected data.",
					pixel_idx, MAX_FRAME_SIZE, configured_width, configured_height, current_frame_id))
	  end

	  //----------------------------------------------------------------
	  // Frame boundary handling
	  //----------------------------------------------------------------
	  if (tr.m_axis_tlast) begin
		// Dump DUT frame to file
		$sformat(dump_name, "results/result%0.3d.raw", current_frame_id);
		dump_fd = $fopen(dump_name, "wb");
		if (dump_fd == 0) begin
		  `uvm_fatal("DMD_SCB",
			$sformatf("Cannot open %s. Ensure 'results' directory exists.", dump_name))
		end

		for (int i = 0; i <= pixel_idx; i++) begin
		  // Dump ARGB bytes
		  $fwrite(dump_fd, "%c%c%c%c",
				  output_pixel_dut[i][31:24], // Red
				  output_pixel_dut[i][23:16], // Green
				  output_pixel_dut[i][15:8],  // Blue
				  output_pixel_dut[i][7:0]);  // Metadata
		end
		$fclose(dump_fd);

		`uvm_info("DMD_SCB",
		  $sformatf("Dumped DUT output frame %0d to %s", current_frame_id, dump_name),
		  UVM_LOW)

		// Reset counters for next frame
		current_x = 0;
		current_y = 0;
		current_frame_id++;

	  end else begin
		// Not last pixel, increment counters normally
		if (current_x == configured_width - 1) begin
		  current_x = 0;
		  current_y++;
		end else begin
		  current_x++;
		end
	  end

	end // valid handshake for output

  endfunction : write

  //----------------------------------------------------------------------------
  // report_phase - end of simulation summary
  //----------------------------------------------------------------------------
  virtual function void report_phase(uvm_phase phase);
	`uvm_info("SCOREBOARD",
	  $sformatf("Scoreboard finished. Dumped %0d output frames.", current_frame_id),
	  UVM_LOW)
  endfunction

endclass : dmd_scoreboard
