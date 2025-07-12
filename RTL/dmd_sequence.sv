/*------------------------------------------------------------------------------
 * File          : dmd_sequence.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jul 6, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class dmd_sequence extends uvm_sequence#(dmd_trans);
  `uvm_object_utils(dmd_sequence)

  // Configuration parameters for the sequence (can be overridden from test)
  string          raw_folder;       // path to "frame000.raw", "frame001.raw", ...
  int unsigned    num_frames;       // how many frames to stream
  int unsigned    width;            // frame width in pixels
  int unsigned    height;           // frame height in pixels
  int unsigned    threshold;        // motion threshold
  bit [31:0]      rgb_pixel;        // Temporary variable to hold pixel data

  // Constructor: Initialize sequence parameters with default values
  function new(string name = "dmd_sequence");
	super.new(name);
	width      = 352;
	height     = 288;
	threshold  = 12;
	num_frames = 141;
	raw_folder = "frames"; 
  endfunction

  virtual task body();
	dmd_trans tr;
	string    fname;
	int       fh;
	byte      r, g, b, z; // For reading 4 bytes (RGB + padding)
	int unsigned frame_size = width * height; // Total pixels per frame
	
	// ------------------------------------------------------------------------
	// Phase 1: Configure the DUT via AXI-Lite Slave (s_axil)
	// ------------------------------------------------------------------------
	tr = dmd_trans::type_id::create("config_trans");
	tr.set_all_inactive(); // Start with all signals inactive

	// Set AXI-Lite configuration signals
	tr.s_axil_valid     = 1;
	tr.s_axil_width     = width;
	tr.s_axil_height    = height;
	tr.s_axil_threshold = threshold;

		start_item(tr);
	finish_item(tr);

	tr = dmd_trans::type_id::create("config_deassert_trans");
	tr.set_all_inactive(); // Ensure s_axil_valid is now 0
	start_item(tr);
	finish_item(tr);

	// ------------------------------------------------------------------------
	// Phase 2: Stream Video Frames via AXI4-Stream Slave (s_axis)
	// ------------------------------------------------------------------------
	for (int unsigned fid = 75; fid < num_frames; fid++) begin
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

  endtask
endclass : dmd_sequence
