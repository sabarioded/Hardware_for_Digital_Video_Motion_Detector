class mp_scoreboard extends uvm_component;
	`uvm_component_utils(mp_scoreboard)

	uvm_analysis_imp#(mp_trans, mp_scoreboard) ap;

	logic [31:0] expected_pixel;
	localparam HIGHLIGHT_COLOR = 32'hFF000000;
	localparam int WIDTH = 352;
	localparam int HEIGHT = 288;
	localparam int DEPTH = WIDTH*HEIGHT;
	
	localparam byte GRAY_R_COEFF = 8'd77;
	localparam byte GRAY_G_COEFF = 8'd150;
	localparam byte GRAY_B_COEFF = 8'd29;
	
	byte background    [0:DEPTH-1];
	byte variance      [0:DEPTH-1];
	byte prev_gray     [0:DEPTH-1];
	
	// Current frame data (populated pixel by pixel)
	bit  motion_map    [0:DEPTH-1];
	logic [31:0] output_pixel [0:DEPTH-1]; // DUT's output for current frame
	logic [31:0] memory_pixel_frame [0:DEPTH-1];

	// Reference output (calculated based on previous frame's data)
	logic [31:0] output_pixel_ref [0:DEPTH-1];

	int    xmin[1:255], ymin[1:255], xmax[1:255], ymax[1:255];
	bit    seen[1:255];
	
	int unsigned error_count;
	int unsigned x;
	int unsigned y;
	string dump_name;
	int    dump_fd;
	int nbrs[$];
	int idx;
	int label_table[0:255];
	
	function new(string name, uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	virtual function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  x = 0;
	  y = 0;
	  error_count  = 0;
	  next_label = 1;
	  ap = new("ap", this);
	  foreach (variance[i]) variance[i] = 2;
	  for (int i = 0; i < 256; i++)
		  label_table[i] = i;  // self-parented
	endfunction

	virtual function void write(mp_trans tr);
	  int idx = y * tr.width + x;
	  byte gray;
	  int  diff, pixel_diff,background_diff;
	  bit  exp_motion;
	  
	  bit [7:0] expected_gray;
	  bit [7:0] expected_prev;    
	  bit [15:0] calc;

	  if (!tr.enable || !tr.pixel_valid) begin
		return;
	  end

	  // Grayscale conversion
	  calc = ((tr.rbg_pixel[31:24]*GRAY_R_COEFF)
			   + (tr.rbg_pixel[23:16]*GRAY_G_COEFF)
			   + (tr.rbg_pixel[15:8] *GRAY_B_COEFF));
	  expected_gray = calc[15:8];

	  expected_prev = (tr.frame_id == 0) ? 8'h00 : prev_gray[idx];

	  prev_gray[idx] = expected_gray;
	  
	  // === VARIANCE NEXT ===
	  diff = (expected_gray > background[idx]) ? (expected_gray - background[idx]) :
		  (background[idx] - expected_gray);

	  // Update variance, clipping between 2 and 255
	  if (diff > variance[idx]) begin
		variance[idx] = (variance[idx] > 253) ? 8'd255 : variance[idx] + 2;
	  end
	  else if (diff < variance[idx]) begin
		variance[idx] = (variance[idx] < 4) ? 8'd2 : variance[idx] - 2;
	  end
	
	  // === BACKGROUND NEXT ===
	  if (tr.wr_background) begin
		background[idx] = expected_gray;
	  end
	  else if (expected_gray >  background[idx]) begin
		background[idx] =  (background[idx] == 8'd255) ? 8'd255 : background[idx] + 1;
	  end
	  else if(expected_gray <  background[idx])begin
		background[idx] = (background[idx] == 8'd0) ? 8'd0 : background[idx] - 1;
	  end  
	  
	  pixel_diff = (expected_gray > expected_prev) ?
			(expected_gray - expected_prev) :
			(expected_prev - expected_gray);

	  background_diff = (expected_gray > background[idx]) ?
				 (expected_gray - background[idx]) :
				 (background[idx] - expected_gray);

	  exp_motion = (pixel_diff > tr.threshold) && (background_diff >= variance[idx]);
	  
	  motion_map[idx] = exp_motion;
	  output_pixel[idx] = tr.highlighted_pixel;
	  memory_pixel_frame[idx] = tr.memory_pixel;
	  
	  // Advance counters and handle end-of-frame logic
	  if (tr.last_in_frame) begin
		if (tr.frame_id >= 0) begin
			//generate_reference_for_frame(motion_map, memory_pixel_frame,output_pixel_ref);
		end			
		  $sformat(dump_name, "results/result%0.3d.raw", tr.frame_id);
		  dump_fd = $fopen(dump_name, "wb");
		  if (dump_fd == 0) begin
			`uvm_fatal("MP_SCB", $sformatf("Cannot open dump file %s", dump_name));
		  end
			
		  for(int i = 0; i < tr.width * tr.height; i++) begin
			$fwrite(dump_fd, "%c%c%c%c",
					output_pixel[i][31:24],
					output_pixel[i][23:16],
					output_pixel[i][15:8],
					output_pixel[i][7:0]
			);
			if(output_pixel[i] != output_pixel_ref[i]) begin
			  `uvm_error("SCOREBOARD", $sformatf(
					  "Mismatch at frame %0d, (idx=%0d): DUT=0x%08h REF=0x%08h",
					   tr.frame_id, i,
					   output_pixel[i], output_pixel_ref[i]
					));
			  error_count++;
			end
		  end
		  $fclose(dump_fd);
		  `uvm_info("MP_SCB", $sformatf("Dumped DUT output to %s", dump_name), UVM_LOW);
	

		// Reset current frame processing variables for next incoming frame
		x = 0;
		y = 0;
		foreach (motion_map[i]) motion_map[i] = 0;
	  end else if(x == tr.width-1) begin
		x = 0;
		y = y+1;
	  end else begin
		x = x+1;
	  end
	endfunction
	
	int x_;
	int y_;
	int ind;
	int top_label;
	int left_label;
	int label_map[0:DEPTH-1];
	int new_label_valid;
	int new_label_value;
	int merge_a;
	int merge_b;
	int merge_labels;
	int current_label;
	int root1;
	int root2;
	int resolved_label;
	int next_label;
	typedef struct packed {
		logic [10:0]  min_x;
		logic [9:0] min_y;
		logic [10:0]  max_x;
		logic [9:0] max_y;
		logic label_active;
		logic is_root;
	} bbox_s;

	bbox_s bank [0:255];
	function generate_reference_for_frame(bit motion_map [0:DEPTH-1], logic [31:0] memory_pixel_frame [0:DEPTH-1], logic [31:0] output_pixel_ref [0:DEPTH-1]);
		x_ = 0;
		y_ = 0;
		ind = 0;
		next_label = 1;
		for (int i = 0; i < 256; i++)
			label_table[i] = i;  // self-parented
		foreach(label_map[i]) label_map[i] = 0;
		for (int i = 0; i < 256; i++) begin
			bank[i].min_x = '1;
			bank[i].min_y = '1;
			bank[i].max_x = 0;
			bank[i].max_y = 0;
			bank[i].label_active = 0;
			bank[i].is_root = 1;
		end
		
		while(ind < DEPTH) begin
			new_label_valid = 0;
			new_label_value = 0;
			merge_a = 0;
			merge_b = 0;
			merge_labels = 0;
			current_label = 0;
			
			ind = y_ * WIDTH + x_;
			if(!motion_map[ind]) continue;
			
			//labeler
			top_label = (y_ > 0) ? label_map[ind-WIDTH+1] : 0;
			left_label = (x_ > 0) ? label_map[ind-1] : 0;
			if(top_label == 0 && left_label == 0) begin
				new_label_valid = 1;
				new_label_value = next_label;
				current_label = next_label;
			end else if(top_label != 0 && left_label == 0) begin
				current_label = left_label;
			end else if(top_label == 0 && left_label != 0) begin
				current_label = top_label;
			end else begin
				if (left_label < top_label) begin
					current_label = left_label;
					merge_labels  = 1;
					merge_a       = left_label;
					merge_b       = top_label;
				  end else if (top_label < left_label) begin
					current_label = top_label;
					merge_labels  = 1;
					merge_a       = top_label;
					merge_b       = left_label;
				  end else begin
					current_label = left_label;
				  end
			end
			if(next_label == 0) next_label = 0;
			else next_label = (new_label_valid) ? next_label+1 : next_label;
			if(next_label > 255)  next_label = 0;
			
			// label_merger
			root1 = label_table[current_label];
			root2 = label_table[root1];
			resolved_label = (root2 == root1) ? root1 : root2;

			if(merge_labels) begin
				label_table[merge_b] = merge_a;
			end
			
			// update boxes
			if (!bank[resolved_label].label_active) begin
				// Initialize on first hit
				bank[resolved_label].min_x = x;
				bank[resolved_label].max_x = x;
				bank[resolved_label].min_y = y;
				bank[resolved_label].max_y = y;
				bank[resolved_label].label_active = 1;
			end else begin
				// Update existing bounding box
				if (x < bank[resolved_label].min_x) bank[resolved_label].min_x = x;
				if (x > bank[resolved_label].max_x) bank[resolved_label].max_x = x;
				if (y < bank[resolved_label].min_y) bank[resolved_label].min_y = y;
				if (y > bank[resolved_label].max_y) bank[resolved_label].max_y = y;
				if(resolved_label != current_label)  bank[resolved_label].is_root = 0;
			end
			
			if(x == WIDTH -1) begin
				x = 0;
				y = y +1;
			end else begin
				x = x + 1;
			end
		end // WHILE  
		
		x = 0;
		y = 0;
		foreach(output_pixel_ref[i]) begin
			for (int i = 1; i < 256; i++) begin
				if (bank[i].label_active && !bank[i].is_root) begin
						if ((x == bank[i].min_x || x == bank[i].max_x) &&
							(bank[i].min_y <= y && y <= bank[i].max_y)) begin
							output_pixel_ref[i] = HIGHLIGHT_COLOR;
						end else if ((y == bank[i].min_y || y == bank[i].max_y) &&
									 (bank[i].min_x <= x && x <= bank[i].max_x)) begin
							output_pixel_ref[i] = HIGHLIGHT_COLOR;
						end
					end
			end
			if(x == WIDTH -1) begin
				x = 0;
				y = y +1;
			end else begin
				x = x + 1;
			end
		end
		
	endfunction


	// Final report phase
	virtual function void report_phase(uvm_phase phase);
	  `uvm_info("SCOREBOARD", $sformatf("Total mismatches = %0d", error_count),
		(error_count==0) ? UVM_LOW : UVM_HIGH);
	endfunction

  endclass: mp_scoreboard