/*------------------------------------------------------------------------------
 * File          : dmd_scoreboard.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jul 6, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class dmd_scoreboard extends uvm_scoreboard;
	`uvm_component_utils(dmd_scoreboard)

	// Analysis port from the dmd_monitor
	uvm_analysis_imp#(dmd_trans, dmd_scoreboard) ap;

	// Fixed parameters for sizing the buffer (should be large enough for max expected frame)
	// Adjust these TB_WIDTH_BITS and TB_HEIGHT_BITS to match the maximum width/height
	// your DUT or testbench expects to configure.
	localparam int TB_WIDTH_BITS       = 11; // Max 2048 pixels (e.g., for 1920)
	localparam int TB_HEIGHT_BITS      = 10; // Max 1024 lines (e.g., for 1080)
	localparam int TB_STREAM_WIDTH     = 32; // Assuming 32-bit pixel data (ARGB)

	localparam int MAX_REF_WIDTH  = (1 << TB_WIDTH_BITS);
	localparam int MAX_REF_HEIGHT = (1 << TB_HEIGHT_BITS);
	localparam int MAX_FRAME_SIZE = MAX_REF_WIDTH * MAX_REF_HEIGHT; // Max buffer size

	// Internal configuration registers (captured from s_axil)
	// These will store the *actual* width and height configured for the current test.
	logic [10:0]  configured_width;
	logic [9:0]   configured_height;
	logic         config_loaded; // Flag to indicate if configuration is loaded

	// Derived parameter: size of the current frame based on configuration
	int unsigned  current_frame_size; // configured_width * configured_height

	// Buffer to store the DUT's output pixels for the current frame
	logic [TB_STREAM_WIDTH-1:0] output_pixel_dut [0:MAX_FRAME_SIZE-1];

	// Pixel counters for current frame processing
	int unsigned current_x; // Current column (pixel) in the frame
	int unsigned current_y; // Current row (line) in the frame
	int unsigned current_frame_id; // Counter for dumped frames

	// File dumping variables
	string dump_name;
	int    dump_fd;

	function new(string name, uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	virtual function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  ap = new("ap", this); // Create analysis imp port

	  // Initialize scoreboard state
	  configured_width = '0;
	  configured_height = '0;
	  config_loaded = 0;
	  current_frame_size = 0;

	  current_x = 0;
	  current_y = 0;
	  current_frame_id = 0;

	  // Clear DUT output buffer
	  foreach (output_pixel_dut[i]) output_pixel_dut[i] = '0;
	endfunction

	// write function: called by monitor's analysis port for each transaction
	virtual function void write(dmd_trans tr);
	  // ---------------------------------------------------------------------
	  // 1. Capture Configuration (S_AXIL)
	  // This section should only execute once when configuration is valid.
	  // ---------------------------------------------------------------------
	  if (tr.s_axil_valid && tr.as_axil_ready && !config_loaded) begin
		configured_width  = tr.s_axil_width;
		configured_height = tr.s_axil_height;
		current_frame_size = configured_width * configured_height;
		config_loaded = 1'b1;
		`uvm_info("DMD_SCB", $sformatf("Config Captured: Width=%0d, Height=%0d. Frame size=%0d pixels.",
										configured_width, configured_height, current_frame_size), UVM_HIGH)
		return; // Process config, then return as this is not a pixel transaction
	  end

	  // ---------------------------------------------------------------------
	  // 2. Gather Output Pixels (M_AXIS)
	  // Only process pixel data if configuration is loaded and output pixel is valid.
	  // ---------------------------------------------------------------------
	  if (!config_loaded || !tr.m_axis_tvalid || !tr.m_axis_tready) begin
		// `uvm_info("DMD_SCB", "Skipping transaction (no config or no output handshake)", UVM_FULL)
		return;
	  end

	  // Calculate linear index for the current pixel
	  int pixel_idx = current_y * configured_width + current_x;

	  // Store DUT's output pixel into the buffer
	  // Ensure pixel_idx is within bounds of MAX_FRAME_SIZE
	  if (pixel_idx < MAX_FRAME_SIZE) begin
		output_pixel_dut[pixel_idx] = tr.m_axis_tdata;
	  end else begin
		`uvm_error("DMD_SCB", $sformatf("Pixel index %0d out of buffer bounds (MAX_FRAME_SIZE=%0d). Configured WxH: %0dx%0d. This might indicate incorrect configuration or TLAST.", pixel_idx, MAX_FRAME_SIZE, configured_width, configured_height));
	  end

	  // ---------------------------------------------------------------------
	  // 3. Handle End-of-Frame and Dump to File
	  // The tr.m_axis_tlast signal indicates the last pixel of a frame.
	  // ---------------------------------------------------------------------
	  if (tr.m_axis_tlast) begin
		`uvm_info("DMD_SCB", $sformatf("End of Output Frame %0d detected. Dumping %0d pixels to file...",
										current_frame_id, current_frame_size), UVM_HIGH)

		// Dump DUT output to file
		// Create 'results' directory in your simulation root if it doesn't exist
		$sformat(dump_name, "results/output_frame_%0.3d.raw", current_frame_id);
		dump_fd = $fopen(dump_name, "wb");
		if (dump_fd == 0) begin
		  `uvm_fatal("DMD_SCB", $sformatf("Cannot open dump file %s. Make sure 'results' directory exists and has write permissions.", dump_name));
		end

		for(int i = 0; i < current_frame_size; i++) begin
		  // Write DUT's output pixel to file (assuming ARGB format)
		  // Note: Most image viewers expect RGB. If your DUT output is ARGB,
		  // you might write all 4 bytes, or just RGB depending on your viewer.
		  // Example for ARGB:
		  $fwrite(dump_fd, "%c%c%c%c",
				  output_pixel_dut[i][31:24], // Alpha byte
				  output_pixel_dut[i][23:16], // Red byte
				  output_pixel_dut[i][15:8],  // Green byte
				  output_pixel_dut[i][7:0]    // Blue byte
		  );
		  // If you only want RGB (e.g., for simple viewers), you might do:
		  // $fwrite(dump_fd, "%c%c%c", output_pixel_dut[i][23:16], output_pixel_dut[i][15:8], output_pixel_dut[i][7:0]);
		end
		$fclose(dump_fd);
		`uvm_info("DMD_SCB", $sformatf("Dumped DUT output frame to %s", dump_name), UVM_LOW);

		// Reset counters for the next frame
		current_x = 0;
		current_y = 0;
		current_frame_id++; // Advance frame counter

	  end else begin // Not end of frame, advance pixel counters
		if (current_x == configured_width - 1) begin
		  current_x = 0;
		  current_y = current_y + 1;
		end else begin
		  current_x = current_x + 1;
		end
	  end
	endfunction

	// Final report phase (simplified)
	virtual function void report_phase(uvm_phase phase);
	  `uvm_info("SCOREBOARD", $sformatf("Scoreboard finished. Dumped %0d output frames.", current_frame_id), UVM_LOW);
	endfunction

endclass : dmd_scoreboard
