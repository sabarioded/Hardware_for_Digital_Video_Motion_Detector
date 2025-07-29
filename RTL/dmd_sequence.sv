/*------------------------------------------------------------------------------
 * File          : dmd_sequence.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jul 6, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class dmd_sequence extends uvm_sequence#(dmd_trans);
	`uvm_object_utils(dmd_sequence)

	// Randomized DUT configuration parameters
	rand int unsigned rand_width;
	rand int unsigned rand_height;
	rand int unsigned rand_threshold;
	int unsigned total_frames;
	int unsigned frame_size;
	
	// Configuration parameters for the sequence (can be overridden from test)
	string          raw_folder;       // path to "frame000.raw", "frame001.raw", ...
	int unsigned    num_frames;       // how many frames to stream
	int unsigned    width;            // frame width in pixels
	int unsigned    height;           // frame height in pixels
	int unsigned    threshold;        // motion threshold
	bit [31:0]      rgb_pixel;        // Temporary variable to hold pixel data

	function new(string name = "dmd_sequence");
	  super.new(name);
	  total_frames = 20;
	  width      = 352;
	  height     = 288;
	  threshold  = 12;
	  num_frames = 225;
	  raw_folder = "frames"; 
	endfunction

	virtual task body();
	  dmd_trans tr;
	  string    fname;
	  int       fh;
	  byte      r, g, b, z; // For reading 4 bytes (RGB + padding)
	  
	  // First, randomize configuration parameters
	  if (!randomize(rand_width, rand_height, rand_threshold)
		   with {
			 rand_width == width;//inside {[64:1290]};
			 rand_height == height;//inside {[64:720]};
			 rand_threshold == threshold;//inside {[1:255]};
		   }) begin
		`uvm_fatal("RAND_SEQ", "Failed to randomize configuration!")
	  end

	  `uvm_info("RAND_SEQ", $sformatf("Random Config width=%0d height=%0d threshold=%0d frames=%0d",
									  rand_width, rand_height, rand_threshold, total_frames), UVM_LOW)

	  // ------------------------------------------------------------------------
	  // Phase 1: Initial Configuration Write
	  // ------------------------------------------------------------------------
	  tr = dmd_trans::type_id::create("rand_config_write");
	  tr.set_all_inactive();

	  tr.s_axil_valid     = 1;
	  tr.s_axil_data[10:0]  = rand_width;
	  tr.s_axil_data[21:11] = rand_height;
	  tr.s_axil_data[29:22] = rand_threshold;

	  start_item(tr);
	  finish_item(tr);

	  // Deassert after config
	  tr = dmd_trans::type_id::create("rand_config_deassert");
	  tr.set_all_inactive();
	  start_item(tr);
	  finish_item(tr);

	  // Calculate pixels/frame
	  frame_size = rand_width * rand_height; 
	  
	  // ------------------------------------------------------------------------
	  // Phase 1: Configure the DUT via AXI-Lite Slave (s_axil)
	  // ------------------------------------------------------------------------

	  tr = dmd_trans::type_id::create("config_deassert_trans");
	  tr.set_all_inactive(); // Ensure s_axil_valid is now 0
	  start_item(tr);
	  finish_item(tr);
	  tr = dmd_trans::type_id::create("config_deassert_trans");
	  tr.set_all_inactive(); // Ensure s_axil_valid is now 0
	  tr.s_axis_tvalid = 1;
	  start_item(tr);
	  finish_item(tr);
	  /*
	  // ------------------------------------------------------------------------
	  // Phase 
	  // ------------------------------------------------------------------------
	  for(int i = 0; i < 5;i++) begin
		  tr = dmd_trans::type_id::create("tr");
		  tr.set_all_inactive();
		  if (!tr.randomize() with {
			// Random pixel data
			s_axis_tdata inside {[32'h00000000:32'hFFFFFFFF]};

			// Random handshake stalls
			s_axis_tvalid == 0;
			m_axis_tready == 0;

			// Random AXI memory handshake toggling
			m_axi_awready == 0;
			m_axi_wready  == 0;
			m_axi_arready == 0;
			m_axi_rvalid  == 0;

			// Occasionally trigger mid-run config writes
			s_axil_valid == 0;
			
		  }) begin
			`uvm_error("RAND_SEQ", "Transaction randomization failed!")
		  end
	  end
	  for(int i = 0; i < 5;i++) begin
		  tr = dmd_trans::type_id::create("tr");
		  tr.set_all_inactive();
		  if (!tr.randomize() with {
			// Random pixel data
			s_axis_tdata inside {[32'h00000000:32'hFFFFFFFF]};

			// Random handshake stalls
			s_axis_tvalid == 1;
			m_axis_tready == 0;

			// Random AXI memory handshake toggling
			m_axi_awready == 0;
			m_axi_wready  == 0;
			m_axi_arready == 0;
			m_axi_rvalid  == 0;

			// Occasionally trigger mid-run config writes
			s_axil_valid == 0;
			
		  }) begin
			`uvm_error("RAND_SEQ", "Transaction randomization failed!")
		  end
	  end
	  for(int i = 0; i < 5;i++) begin
		  tr = dmd_trans::type_id::create("tr");
		  tr.set_all_inactive();
		  if (!tr.randomize() with {
			// Random pixel data
			s_axis_tdata inside {[32'h00000000:32'hFFFFFFFF]};

			// Random handshake stalls
			s_axis_tvalid == 0;
			m_axis_tready == 1;

			// Random AXI memory handshake toggling
			m_axi_awready == 0;
			m_axi_wready  == 0;
			m_axi_arready == 0;
			m_axi_rvalid  == 0;

			// Occasionally trigger mid-run config writes
			s_axil_valid == 0;
			
		  }) begin
			`uvm_error("RAND_SEQ", "Transaction randomization failed!")
		  end
	  end
	  for(int i = 0; i < 5;i++) begin
		  tr = dmd_trans::type_id::create("tr");
		  tr.set_all_inactive();
		  if (!tr.randomize() with {
			// Random pixel data
			s_axis_tdata inside {[32'h00000000:32'hFFFFFFFF]};

			// Random handshake stalls
			s_axis_tvalid == 1;
			m_axis_tready == 1;

			// Random AXI memory handshake toggling
			m_axi_awready == 0;
			m_axi_wready  == 0;
			m_axi_arready == 0;
			m_axi_rvalid  == 0;

			// Occasionally trigger mid-run config writes
			s_axil_valid == 0;
			
		  }) begin
			`uvm_error("RAND_SEQ", "Transaction randomization failed!")
		  end
	  end
	  
	  for (int frame_idx = 0; frame_idx < total_frames; frame_idx++) begin

		for (int pix = 0; pix < frame_size; pix++) begin
		  tr = dmd_trans::type_id::create($sformatf("rand_pix_f%0d_p%0d", frame_idx, pix));
		  tr.set_all_inactive();

		  // ---------------- RANDOMIZATION CONSTRAINTS ----------------
		  if (!tr.randomize() with {
			// Random pixel data
			s_axis_tdata inside {[32'h00000000:32'hFFFFFFFF]};

			// Random handshake stalls
			s_axis_tvalid dist {1 := 80, 0 := 20};
			m_axis_tready dist {1 := 80, 0 := 20};

			// Random AXI memory handshake toggling
			m_axi_awready dist {1 := 80, 0 := 20};
			m_axi_wready  dist {1 := 80, 0 := 20};
			m_axi_arready dist {1 := 80, 0 := 20};
			m_axi_rvalid  dist {1 := 80, 0 := 20};

			// Occasionally trigger mid-run config writes
			s_axil_valid dist {1 := 80, 0 := 20};

			// Force frame boundary tlast on last pixel
			s_axis_tlast  == (pix == frame_size - 1);
			
		  }) begin
			`uvm_error("RAND_SEQ", "Transaction randomization failed!")
		  end

		  // Add frame_id for debug
		  tr.frame_id = frame_idx;

		  // Send the transaction
		  start_item(tr);
		  finish_item(tr);

		  // Random idle gap between pixels (forces handshake combinations)
		  if ($urandom_range(0,6) == 0) begin
			repeat($urandom_range(1,3)) #(10ns);
		  end
		end // pixel loop

		// After finishing a frame, insert random gap before next frame
		repeat($urandom_range(2,5)) #(10ns);

		// Occasionally trigger a config reload mid-run
		if ($urandom_range(0,10) == 0) begin
		  tr = dmd_trans::type_id::create($sformatf("rand_config_reload_f%0d", frame_idx));
		  tr.set_all_inactive();
		  tr.s_axil_valid = 1;
		  tr.s_axil_data[10:0]  = $urandom_range(64,1280);
		  tr.s_axil_data[21:11] = $urandom_range(64,720);
		  tr.s_axil_data[29:22] = $urandom_range(1,255);
		  start_item(tr);
		  finish_item(tr);

		  tr = dmd_trans::type_id::create("rand_config_reload_deassert");
		  tr.set_all_inactive();
		  start_item(tr);
		  finish_item(tr);
		end
	  end // frame loop
	  */

	  // ------------------------------------------------------------------------
	  // Phase 2: Stream Video Frames via AXI4-Stream Slave (s_axis)
	  // ------------------------------------------------------------------------
	  for (int unsigned fid = 0; fid < num_frames; fid++) begin
		string fid_str;
		if (fid < 10)
		  $sformat(fid_str, "00%0d", fid);
		else if (fid < 100)
		  $sformat(fid_str, "0%0d", fid);
		else
		  $sformat(fid_str, "%0d", fid);
		$sformat(fname, "%s/frame_%s.raw", raw_folder, fid_str);
		
		// Open raw file in binary read mode
		fh = $fopen(fname, "rb");
		if (fh == 0) begin
		  `uvm_fatal("PIXEL_SEQ", $sformatf("Cannot open raw file: %s. Ensure 'frames' directory exists and contains files like frame_000.raw", fname))
		end

		// Read and stream every pixel for the current frame
		for (int unsigned pidx = 0; pidx < frame_size; pidx++) begin
		  // Read four bytes: R, G, B, padding
		  r = $fgetc(fh);
		  g = $fgetc(fh);
		  b = $fgetc(fh);
		  z = $fgetc(fh);

		  rgb_pixel = {r, g, b, 8'h00};

		  // Create a new transaction for each pixel
		  tr = dmd_trans::type_id::create($sformatf("pix_f%0d_p%0d", fid, pidx));
		  tr.set_all_inactive(); // Reset all signals to inactive defaults
		  //tr.randomize();

		  // Directly assign values to the transaction fields
		  tr.s_axis_tvalid = 1;
		  tr.s_axis_tdata  = rgb_pixel;
		  tr.s_axis_tlast  = (pidx == frame_size - 1); // Assert tlast on the very last pixel of the frame
		  tr.frame_id      = fid; // For monitoring/debugging

		  // Send the pixel transaction
		  start_item(tr);
		  finish_item(tr);
		end
		$fclose(fh); // Close the raw file after streaming all pixels for the frame

	  end
	  
	  // ------------------------------------------------------------------------
	  // Phase 2: Random Frame Streaming
	  // ------------------------------------------------------------------------
	  for(int i = 0; i < 5;i++) begin
		  tr = dmd_trans::type_id::create("tr");
		  tr.set_all_inactive();
		  if (!tr.randomize() with {
			// Random pixel data
			s_axis_tdata inside {[32'h00000000:32'hFFFFFFFF]};

			// Random handshake stalls
			s_axis_tvalid == 0;
			m_axis_tready == 0;

			// Random AXI memory handshake toggling
			m_axi_awready == 0;
			m_axi_wready  == 0;
			m_axi_arready == 0;
			m_axi_rvalid  == 0;

			// Occasionally trigger mid-run config writes
			s_axil_valid == 0;
			
		  }) begin
			`uvm_error("RAND_SEQ", "Transaction randomization failed!")
		  end
	  end
	  for(int i = 0; i < 5;i++) begin
		  tr = dmd_trans::type_id::create("tr");
		  tr.set_all_inactive();
		  if (!tr.randomize() with {
			// Random pixel data
			s_axis_tdata inside {[32'h00000000:32'hFFFFFFFF]};

			// Random handshake stalls
			s_axis_tvalid == 1;
			m_axis_tready == 0;

			// Random AXI memory handshake toggling
			m_axi_awready == 0;
			m_axi_wready  == 0;
			m_axi_arready == 0;
			m_axi_rvalid  == 0;

			// Occasionally trigger mid-run config writes
			s_axil_valid == 0;
			
		  }) begin
			`uvm_error("RAND_SEQ", "Transaction randomization failed!")
		  end
	  end
	  for(int i = 0; i < 5;i++) begin
		  tr = dmd_trans::type_id::create("tr");
		  tr.set_all_inactive();
		  if (!tr.randomize() with {
			// Random pixel data
			s_axis_tdata inside {[32'h00000000:32'hFFFFFFFF]};

			// Random handshake stalls
			s_axis_tvalid == 0;
			m_axis_tready == 1;

			// Random AXI memory handshake toggling
			m_axi_awready == 0;
			m_axi_wready  == 0;
			m_axi_arready == 0;
			m_axi_rvalid  == 0;

			// Occasionally trigger mid-run config writes
			s_axil_valid == 0;
			
		  }) begin
			`uvm_error("RAND_SEQ", "Transaction randomization failed!")
		  end
	  end
	  for(int i = 0; i < 5;i++) begin
		  tr = dmd_trans::type_id::create("tr");
		  tr.set_all_inactive();
		  if (!tr.randomize() with {
			// Random pixel data
			s_axis_tdata inside {[32'h00000000:32'hFFFFFFFF]};

			// Random handshake stalls
			s_axis_tvalid == 1;
			m_axis_tready == 1;

			// Random AXI memory handshake toggling
			m_axi_awready == 0;
			m_axi_wready  == 0;
			m_axi_arready == 0;
			m_axi_rvalid  == 0;

			// Occasionally trigger mid-run config writes
			s_axil_valid == 0;
			
		  }) begin
			`uvm_error("RAND_SEQ", "Transaction randomization failed!")
		  end
	  end
	  
	 /* for (int frame_idx = 0; frame_idx < total_frames; frame_idx++) begin

		for (int pix = 0; pix < frame_size; pix++) begin
		  tr = dmd_trans::type_id::create($sformatf("rand_pix_f%0d_p%0d", frame_idx, pix));
		  tr.set_all_inactive();

		  // ---------------- RANDOMIZATION CONSTRAINTS ----------------
		  if (!tr.randomize() with {
			// Random pixel data
			s_axis_tdata inside {[32'h00000000:32'hFFFFFFFF]};

			// Random handshake stalls
			s_axis_tvalid dist {1 := 80, 0 := 20};
			m_axis_tready dist {1 := 80, 0 := 20};

			// Random AXI memory handshake toggling
			m_axi_awready dist {1 := 80, 0 := 20};
			m_axi_wready  dist {1 := 80, 0 := 20};
			m_axi_arready dist {1 := 80, 0 := 20};
			m_axi_rvalid  dist {1 := 80, 0 := 20};

			// Occasionally trigger mid-run config writes
			s_axil_valid dist {1 := 80, 0 := 20};

			// Force frame boundary tlast on last pixel
			s_axis_tlast  == (pix == frame_size - 1);
			
		  }) begin
			`uvm_error("RAND_SEQ", "Transaction randomization failed!")
		  end

		  // Add frame_id for debug
		  tr.frame_id = frame_idx;

		  // Send the transaction
		  start_item(tr);
		  finish_item(tr);

		  // Random idle gap between pixels (forces handshake combinations)
		  if ($urandom_range(0,6) == 0) begin
			repeat($urandom_range(1,3)) #(10ns);
		  end
		end // pixel loop

		// After finishing a frame, insert random gap before next frame
		repeat($urandom_range(2,5)) #(10ns);

		// Occasionally trigger a config reload mid-run
		if ($urandom_range(0,10) == 0) begin
		  tr = dmd_trans::type_id::create($sformatf("rand_config_reload_f%0d", frame_idx));
		  tr.set_all_inactive();
		  tr.s_axil_valid = 1;
		  tr.s_axil_data[10:0]  = $urandom_range(64,1280);
		  tr.s_axil_data[21:11] = $urandom_range(64,720);
		  tr.s_axil_data[29:22] = $urandom_range(1,255);
		  start_item(tr);
		  finish_item(tr);

		  tr = dmd_trans::type_id::create("rand_config_reload_deassert");
		  tr.set_all_inactive();
		  start_item(tr);
		  finish_item(tr);
		end
	  end // frame loop*/
	  

	  

	endtask

  endclass : dmd_sequence
