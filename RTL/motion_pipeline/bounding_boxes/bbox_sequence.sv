/*------------------------------------------------------------------------------
 * File          : bbox_sequence.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jun 29, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class bbox_sequence extends uvm_sequence#(bbox_trans);
  `uvm_object_utils(bbox_sequence)

  int num_frames  = 4;
  int width_cfg   = 352;
  int height_cfg  = 288;

  localparam int MAX_BLOBS = 20;

  // Store original individual blob coordinates as a queue for easy access during pixel generation
  // This will represent the "pre-merge" state for the driver's pixel stream
  typedef struct {
	int x0, y0, x1, y1;
  } blob_info_t;
  blob_info_t initial_frame_blobs[$]; // Renamed for clarity - these are the original blobs for the current frame

  // Queue to store the final merged blobs for scoreboard expectation
  blob_info_t merged_blobs_for_scoreboard[$]; // Renamed active_blobs for clarity

  function new(string name = "bbox_sequence");
	super.new(name);
  endfunction

  virtual task body();
	bbox_trans      tr;     // Transaction sent to the driver (pixel stream)
	bbox_trans      exp_tr; // Transaction sent to the scoreboard (merged blobs)
	bbox_sequencer  seqr_h;
	int             total_pixels;
	bit             merged_flag; // Flag to indicate if a merge occurred in a pass
	int             initial_blobs_count;

	if (!$cast(seqr_h, this.get_sequencer())) begin
	  `uvm_fatal("SEQ_CAST", "Sequencer is not a bbox_sequencer")
	end

	for (int f = 0; f < num_frames; f++) begin
	  void'(std::randomize(initial_blobs_count)
			with { initial_blobs_count inside {[1:MAX_BLOBS]}; });

	  // Clear queues for the new frame
	  initial_frame_blobs.delete();
	  merged_blobs_for_scoreboard.delete(); // This will be built from initial_frame_blobs

	  // 1. Generate initial random blobs and populate initial_frame_blobs
	  // These are the pre-merge blobs that the driver will effectively "see"
	  for (int b = 0; b < initial_blobs_count; b++) begin
		int l_x0, l_y0, l_x1, l_y1; // Local variables for randomizing
		void'(std::randomize(l_x0) with { l_x0 inside {[0:width_cfg-2]}; });
		void'(std::randomize(l_y0) with { l_y0 inside {[0:height_cfg-2]}; });
		void'(std::randomize(l_x1)
			with { l_x1 inside {[ l_x0+1 : width_cfg-1 ]}; });
		void'(std::randomize(l_y1)
			with { l_y1 inside {[ l_y0+1 : height_cfg-1 ]}; });

		initial_frame_blobs.push_back('{ x0: l_x0,
									   y0: l_y0,
									   x1: l_x1,
									   y1: l_y1 });

		// Also push to merged_blobs_for_scoreboard initially, then merge from this list
		merged_blobs_for_scoreboard.push_back('{ x0: l_x0,
											   y0: l_y0,
											   x1: l_x1,
											   y1: l_y1 });
	  end
	  
	  // *** Print original (pre-merge) blobs ***
	  /*foreach (initial_frame_blobs[i]) begin
		`uvm_info("SEQ", $sformatf(
		  "Frame %0d Original blob %0d: (%0d,%0d)-(%0d,%0d)",
			f+1, i,
			initial_frame_blobs[i].x0,
			initial_frame_blobs[i].y0,
			initial_frame_blobs[i].x1,
			initial_frame_blobs[i].y1
		), UVM_LOW);
	  end*/

	  // 2. Perform merging on a *copy* of the initial blobs to get the expected merged state
	  // The `merged_blobs_for_scoreboard` queue will be modified by the merging logic.
	  do begin
		merged_flag = 0; // Reset merged flag for each pass

		for (int i = merged_blobs_for_scoreboard.size() - 1; i >= 0; i--) begin
		  for (int j = i - 1; j >= 0; j--) begin
			// Check for overlap/adjacency (no gap condition)
			if (!( (merged_blobs_for_scoreboard[i].x1 + 1 < merged_blobs_for_scoreboard[j].x0) ||
				  (merged_blobs_for_scoreboard[i].x0 > merged_blobs_for_scoreboard[j].x1 + 1) ||
				  (merged_blobs_for_scoreboard[i].y1 + 1 < merged_blobs_for_scoreboard[j].y0) ||
				  (merged_blobs_for_scoreboard[i].y0 > merged_blobs_for_scoreboard[j].y1 + 1) ))
			begin
			  // If no gap, they overlap or touch/abut. Perform union.
			  merged_blobs_for_scoreboard[i].x0 = (merged_blobs_for_scoreboard[i].x0 < merged_blobs_for_scoreboard[j].x0) ? merged_blobs_for_scoreboard[i].x0 : merged_blobs_for_scoreboard[j].x0;
			  merged_blobs_for_scoreboard[i].y0 = (merged_blobs_for_scoreboard[i].y0 < merged_blobs_for_scoreboard[j].y0) ? merged_blobs_for_scoreboard[i].y0 : merged_blobs_for_scoreboard[j].y0;
			  merged_blobs_for_scoreboard[i].x1 = (merged_blobs_for_scoreboard[i].x1 > merged_blobs_for_scoreboard[j].x1) ? merged_blobs_for_scoreboard[i].x1 : merged_blobs_for_scoreboard[j].x1;
			  merged_blobs_for_scoreboard[i].y1 = (merged_blobs_for_scoreboard[i].y1 > merged_blobs_for_scoreboard[j].y1) ? merged_blobs_for_scoreboard[i].y1 : merged_blobs_for_scoreboard[j].y1;

			  merged_blobs_for_scoreboard.delete(j);
			  merged_flag = 1;
			  break;
			end
		  end
		  if (merged_flag) break;
		end
	  end while (merged_flag);

	  // 3. Send the FINAL MERGED blobs to the scoreboard via exp.write()
	  for (int b = 0; b < merged_blobs_for_scoreboard.size(); b++) begin
		exp_tr = bbox_trans::type_id::create(
		  $sformatf("exp_tr_f%0d_merged_b%0d", f, b)
		);
		exp_tr.frame_id  = f + 2;
		exp_tr.bbox_label= b;
		exp_tr.bbox_min_x= merged_blobs_for_scoreboard[b].x0;
		exp_tr.bbox_min_y= merged_blobs_for_scoreboard[b].y0;
		exp_tr.bbox_max_x= merged_blobs_for_scoreboard[b].x1;
		exp_tr.bbox_max_y= merged_blobs_for_scoreboard[b].y1;
		seqr_h.exp.write(exp_tr);
	  end

	  // 4. Stream pixel-by-pixel motion map to the driver based on PRE-MERGE blobs
	  total_pixels = width_cfg * height_cfg;
	  for (int idx = 0; idx < total_pixels; idx++) begin
		int px      = idx % width_cfg;
		int py      = idx / width_cfg;
		bit motion = 0;

		// Determine motion based on the ORIGINAL (pre-merge) blobs for the driver's pixel stream
		for (int b = 0; b < initial_frame_blobs.size(); b++) begin
		  if ((px >= initial_frame_blobs[b].x0) && (px <= initial_frame_blobs[b].x1)
		   && (py >= initial_frame_blobs[b].y0) && (py <= initial_frame_blobs[b].y1)) begin
			motion = 1;
			break; // Pixel is inside one of the original blobs
		  end
		end

		tr = bbox_trans::type_id::create(
		  $sformatf("tr_f%0d_pix%0d", f, idx)
		);
		tr.randomize() with {
		  tr.enable        == 1;
		  tr.motion_pixel  == motion; // This is the key: motion based on original blobs
		  tr.last_in_frame == (idx == total_pixels - 1);
		  tr.width         == width_cfg;
		  tr.height        == height_cfg;
		  tr.frame_id      == f;
		};

		start_item(tr);
		finish_item(tr);
	  end
	end // end for each frame

	total_pixels = width_cfg * height_cfg;
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
	  for (int idx = 0; idx < total_pixels; idx++) begin
		  tr = bbox_trans::type_id::create("tr_final_zero");
		  tr.randomize() with {
			tr.enable        == 1;
			tr.motion_pixel  == 0;
			tr.last_in_frame == (idx == total_pixels - 1);
			tr.width         == width_cfg;
			tr.height        == height_cfg;
			tr.frame_id      == num_frames+1;
		  };
	  start_item(tr);
	  finish_item(tr);
	end
  endtask : body
endclass : bbox_sequence
