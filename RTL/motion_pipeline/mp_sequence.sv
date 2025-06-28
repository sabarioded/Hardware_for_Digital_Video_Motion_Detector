/*------------------------------------------------------------------------------
 * File          : mp_seuence.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jun 11, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mp_sequence extends uvm_sequence#(mp_trans);
  `uvm_object_utils(mp_sequence)

  // Configuration
  string          raw_folder;       // path to "frame000.raw", "frame001.raw", ...
  int unsigned    num_frames;       // how many frames to stream
  int unsigned    width;            // frame width in pixels
  int unsigned    height;           // frame height in pixels
  int unsigned    threshold;        // motion threshold
  bit [31:0] rbg_pixel;
  bit [31:0] memory_pixel;
  bit [31:0] prev_frame_rbg[];

  function new(string name = "mp_sequence");
	super.new(name);
	width=352;
	height=288;
	threshold=8;
	num_frames=141;
	raw_folder="frames";
  endfunction

  virtual task body();
	mp_trans       tr;
	string         fname;
	int            fh;
	byte           r, g, b, z;
	int unsigned   frame_size = width * height;
	prev_frame_rbg = new[frame_size];

	// Loop over each frame
	for (int unsigned fid = 75; fid < num_frames; fid++) begin
	  // Build file name
		//$sformat(fname, "%s/frame_%0.3d.raw", raw_folder, fid);
		string fid_str;

		if (fid < 10)
		  $sformat(fid_str, "00%0d", fid);
		else if (fid < 100)
		  $sformat(fid_str, "0%0d", fid);
		else
		  $sformat(fid_str, "%0d", fid);

		$sformat(fname, "%s/frame_%s.raw", raw_folder, fid_str);
		//`uvm_info("DEBUG", $sformatf("Opening file: %s", fname), UVM_LOW)

	  // Open raw file
	  fh = $fopen(fname, "rb");
	  if (fh == 0) begin
		`uvm_fatal("PIXEL_SEQ", $sformatf("Cannot open raw file: %s", fname))
	  end

	  // Read and stream every pixel
	  for (int unsigned pidx = 0; pidx < frame_size; pidx++) begin
		// Read four bytes: R, G, B, padding
		r = $fgetc(fh);
		g = $fgetc(fh);
		b = $fgetc(fh);
		z = $fgetc(fh);
		
		rbg_pixel = {r, g, b, 8'h00};
		
		if (fid == 0)
			memory_pixel = 32'h00000000;  // zero for first frame
		  else
			memory_pixel = prev_frame_rbg[pidx];
		
		// Save the current pixel for the next frame
		prev_frame_rbg[pidx] = rbg_pixel;
		
		// Create transaction
		tr = mp_trans::type_id::create($sformatf("tr_f%0d_p%0d", fid, pidx));
		tr.frame_id       = fid;
		tr.width          = width;
		tr.height         = height;
		tr.enable         = 1;
		tr.wr_background  = (fid == 0);
		tr.last_in_frame  = (pidx == frame_size - 1);
		tr.threshold      = threshold;
		tr.rbg_pixel      = rbg_pixel;
		tr.memory_pixel   = memory_pixel;

		// Send transaction
		start_item(tr);
		finish_item(tr);
	  end

	  $fclose(fh);
	end
	for (int unsigned pidx = 0; pidx < frame_size; pidx++) begin
		
		rbg_pixel = '0;
		
		memory_pixel = prev_frame_rbg[pidx];
		
		// Save the current pixel for the next frame
		prev_frame_rbg[pidx] = rbg_pixel;
		
		// Create transaction
		tr = mp_trans::type_id::create("tr");
		tr.frame_id       = num_frames;
		tr.width          = width;
		tr.height         = height;
		tr.enable         = 1;
		tr.wr_background  = 0;
		tr.last_in_frame  = (pidx == frame_size - 1);
		tr.threshold      = threshold;
		tr.rbg_pixel      = rbg_pixel;
		tr.memory_pixel   = memory_pixel;

		// Send transaction
		start_item(tr);
		finish_item(tr);
	  end
	
  endtask

endclass : mp_sequence

