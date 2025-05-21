/*------------------------------------------------------------------------------
 * File          : fm_sequence.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 15, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class fm_sequence extends uvm_sequence#(fm_trans);
	`uvm_object_utils(fm_sequence)

	// configuration
	int 		wr_flag;
	int         num_frames;
	int         width;
	int         height;

	function new(string name = "fm_sequence");
	  super.new(name);
	  wr_flag = 1;
	  num_frames  = 100;
	  width       = 32;
	  height      = 24;
	endfunction

	virtual task body();
	  fm_trans  tr;
	 
	  for (int f = 0; f < num_frames; f++) begin
		for (int i = 0; i < width*height; i++) begin
		  // create and drive transaction
		  tr = fm_trans::type_id::create(
				{get_name(), $sformatf("_f%0d_p%0d", f, i)});
		  start_item(tr);
			assert(tr.randomize() with {
			  enable         == 1;
			  pixel[7:0]   == 8'h00;
			  pixel[15:8] dist { [0:20] := 10, [21:235] := 80, [236:255] := 10 };
			  pixel[23:16] dist { [0:20] := 10, [21:235] := 80, [236:255] := 10 };
			  pixel[31:24] dist { [0:20] := 10, [21:235] := 80, [236:255] := 10 };
			  last_in_frame  == (i == width*height-1);
			  wr_background == wr_flag;
			});
		  finish_item(tr);
		end
		wr_flag = 0;
	  end
	endtask
  endclass

class fm_sequence_readfile extends uvm_sequence#(fm_trans);
	`uvm_object_utils(fm_sequence)

	// configuration
	string      raw_folder;
	int         num_frames;
	int         width;
	int         height;

	function new(string name = "fm_sequence");
	  super.new(name);
	  raw_folder = "frames";
	  num_frames  = 6;
	  width       = 352;
	  height      = 288;
	endfunction

	virtual task body();
	  fm_trans  tr;
	  string    fname;
	  integer   file, read_count;
	  bit [31:0] px_data;

	  for (int f = 0; f < num_frames; f++) begin
		$sformat(fname, "%s/frame_%03d.raw", raw_folder, f);
		file = $fopen(fname, "rb");
		if (file == 0) begin
		  `uvm_error(get_full_name(),
			$sformatf("Cannot open %s", fname));
		  continue;
		end

		for (int i = 0; i < width*height; i++) begin
		  read_count = $fread(px_data, file);
		  if (read_count == 0) begin
			`uvm_error(get_full_name(),
			  $sformatf("Unexpected EOF in %s at pixel %0d", fname, i));
			break;
		  end

		  // create and drive transaction
		  tr = fm_trans::type_id::create(
				{get_name(), $sformatf("_f%0d_p%0d", f, i)});
		  start_item(tr);
			assert(tr.randomize() with {
			  enable         == 1;
			  pixel          == px_data;
			  last_in_frame  == (i == width*height-1);
			});
		  finish_item(tr);
		end

		$fclose(file);
	  end
	endtask
  endclass
