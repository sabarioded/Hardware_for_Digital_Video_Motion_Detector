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
		width       = 352;
		height      = 288;
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
				 enable     ==1; // dist { 1 := 90, 0 := 10};//  == 1;
				 pixel[7:0]  dist { [0:20] := 20, [21:235] := 60, [236:255] := 20 };
				 pixel[15:8] dist { [0:20] := 20, [21:235] := 60, [236:255] := 20 };
				 pixel[23:16] dist { [0:20] := 20, [21:235] := 60, [236:255] := 20 };
				 pixel[31:24] dist { [0:20] := 20, [21:235] := 60, [236:255] := 20 };
				 last_in_frame  == (i == width*height-1);
				 wr_background == wr_flag;
				 threshold == threshold_val;
			   });
			 finish_item(tr);
		   end
		   wr_flag = 0;
		 end
		 
		 // ALL MIN PIXEL
		 for (int i = 0; i < width*height; i++) begin
			 // create and drive transaction
			 tr = mmg_trans::type_id::create(
				   {get_name(), $sformatf("_i%0d_MIN", i)});
			 start_item(tr);
			   assert(tr.randomize() with {
				 enable         == 1;
				 pixel[7:0]   == 8'h00;
				 pixel[15:8]  == 8'h00;
				 pixel[23:16] == 8'h00;
				 pixel[31:24] == 8'h00;
				 last_in_frame  == (i == width*height-1);
				 wr_background == wr_flag;
				 threshold == threshold_val;
			   });
			 finish_item(tr);
		 end
		 // ALL MAX PIXEL
		 for (int i = 0; i < width*height; i++) begin
			 // create and drive transaction
			 tr = mmg_trans::type_id::create(
				   {get_name(), $sformatf("_i%0d_MAX", i)});
			 start_item(tr);
			   assert(tr.randomize() with {
				 enable         == 1;
				 pixel[7:0]   == 8'hff;
				 pixel[15:8]  == 8'hff;
				 pixel[23:16] == 8'hff;
				 pixel[31:24] == 8'hff;
				 last_in_frame  == (i == width*height-1);
				 wr_background == wr_flag;
				 threshold == threshold_val;
			   });
			 finish_item(tr);
		 end
	endtask
endclass