/*------------------------------------------------------------------------------
 * File          : simple_blob_sequence.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 27, 2025
 * Description   : UVM sequence generating a random # of blobs per frame,
 *                merging any that touch/overlap/abut, sending them to the scoreboard,
 *                and then streaming pixel traffic (motion map) for those blobs.
 *------------------------------------------------------------------------------*/

class bbox_sequence extends uvm_sequence#(bbox_trans);
  `uvm_object_utils(bbox_sequence)

  // Sequence parameters
  int num_frames  = 10;
  int width_cfg   = 352;
  int height_cfg  = 288;

  // Blob parameters
  localparam int MAX_BLOBS = 20;

  int x0   [MAX_BLOBS];
  int y0   [MAX_BLOBS];
  int x1   [MAX_BLOBS];
  int y1   [MAX_BLOBS];

  function new(string name = "bbox_sequence");
	super.new(name);
  endfunction

  virtual task body();
	bbox_trans     tr;
	bbox_trans     exp_tr;
	bbox_sequencer seqr_h;
	int            total_pixels;
	bit            merged;
	int            initial_blobs;
	int            blob_count;

	// Downcast to our custom sequencer type
	if (!$cast(seqr_h, this.get_sequencer())) begin
	  `uvm_fatal("SEQ_CAST", "Sequencer is not a bbox_sequencer")
	end

	// Loop over each frame:
	for (int f = 0; f < num_frames; f++) begin
	  void'(std::randomize(initial_blobs)
			 with { initial_blobs inside {[1:MAX_BLOBS]}; });

	  for (int b = 0; b < initial_blobs; b++) begin
		void'(std::randomize(x0[b]) with { x0[b] inside {[0:width_cfg-2]}; });
		void'(std::randomize(y0[b]) with { y0[b] inside {[0:height_cfg-2]}; });
		void'(std::randomize(x1[b])
			   with { x1[b] inside {[ x0[b]+1 : width_cfg-1 ]}; });
		void'(std::randomize(y1[b])
			   with { y1[b] inside {[ y0[b]+1 : height_cfg-1 ]}; });
	  end

	  blob_count = initial_blobs;

	  // Merge any that touch, overlap, or abut (4-connectivity includes edge-touching)
	  do begin
		merged = 0;
		for (int i = 0; i < blob_count; i++) begin
		  if (merged) break;
		  for (int j = i+1; j < blob_count; j++) begin
			// Check separation with a one-pixel gap; if no gap, merge
			if (!( (x1[i] + 1 < x0[j])       // completely left with gap
				|| (x0[i] > x1[j] + 1)       // completely right with gap
				|| (y1[i] + 1 < y0[j])       // completely above with gap
				|| (y0[i] > y1[j] + 1) ))    // completely below with gap
			begin
			  // Union bounding boxes
			  x0[i] = (x0[i] < x0[j]) ? x0[i] : x0[j];
			  y0[i] = (y0[i] < y0[j]) ? y0[i] : y0[j];
			  x1[i] = (x1[i] > x1[j]) ? x1[i] : x1[j];
			  y1[i] = (y1[i] > y1[j]) ? y1[i] : y1[j];

			  // Swap last into j and shrink
			  x0[j] = x0[blob_count-1];
			  y0[j] = y0[blob_count-1];
			  x1[j] = x1[blob_count-1];
			  y1[j] = y1[blob_count-1];
			  blob_count--;
			  merged = 1;
			  break;
			end
		  end
		end
	  end while (merged);

	  // Send all final blobs to the scoreboard via exp.write()
	  for (int b = 0; b < blob_count; b++) begin
		exp_tr = bbox_trans::type_id::create(
		  $sformatf("exp_tr_f%0d_b%0d", f, b)
		);
		exp_tr.frame_id  = f + 1;
		exp_tr.bbox_label= b;
		exp_tr.bbox_min_x= x0[b];
		exp_tr.bbox_min_y= y0[b];
		exp_tr.bbox_max_x= x1[b];
		exp_tr.bbox_max_y= y1[b];
		seqr_h.exp.write(exp_tr);
	  end

	  // Stream pixel-by-pixel motion map
	  total_pixels = width_cfg * height_cfg;
	  for (int idx = 0; idx < total_pixels; idx++) begin
		int px     = idx % width_cfg;
		int py     = idx / width_cfg;
		bit motion = 0;

		for (int b = 0; b < blob_count; b++) begin
		  if ((px >= x0[b]) && (px <= x1[b]) 
		   && (py >= y0[b]) && (py <= y1[b])) begin
			motion = 1;
			break;
		  end
		end

		tr = bbox_trans::type_id::create(
		  $sformatf("tr_f%0d_pix%0d", f, idx)
		);
		tr.randomize() with {
		  tr.enable        == 1;
		  tr.motion_pixel  == motion;
		  tr.last_in_frame == (idx == total_pixels - 1);
		  tr.width         == width_cfg;
		  tr.height        == height_cfg;
		  tr.frame_id      == f;
		};
		start_item(tr);
		finish_item(tr);
	  end
	end

	// Final flush zeros
	for (int idx = 0; idx < total_pixels; idx++) begin
	  tr = bbox_trans::type_id::create("tr_final_zero");
	  tr.randomize() with {
		tr.enable        == 1;
		tr.motion_pixel  == 0;
		tr.last_in_frame == (idx == total_pixels - 1);
		tr.width         == width_cfg;
		tr.height        == height_cfg;
		tr.frame_id      == num_frames;
	  };
	  start_item(tr);
	  finish_item(tr);
	end
  endtask : body
endclass : bbox_sequence
