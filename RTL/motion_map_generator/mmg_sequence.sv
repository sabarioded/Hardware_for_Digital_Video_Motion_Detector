/*------------------------------------------------------------------------------
 * File          : mmg_sequence.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 17, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class mmg_sequence extends uvm_sequence #(mmg_trans);
	`uvm_object_utils(mmg_sequence)
	
	// configuration
	int 		wr_flag;
	int         num_frames;
	int         width;
	int         height;
	int 		threshold_val;
	
	function new(string name = "mmg_sequence");
		super.new(name);
		wr_flag = 1;
		num_frames  = 10;
		width       = 32;
		height      = 24;
		threshold_val = 12;
	endfunction
	
	virtual task body();
		mmg_trans  tr;
		
		 for (int f = 0; f < num_frames; f++) begin
		   for (int i = 0; i < width*height; i++) begin
			 // create and drive transaction
			 tr = mmg_trans::type_id::create(
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
				 threshold == threshold_val;
			   });
			 finish_item(tr);
		   end
		   wr_flag = 0;
		   end
	endtask
endclass