/*------------------------------------------------------------------------------
 * File          : motion_detector_sequence.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class motion_detector_sequence extends uvm_sequence #(motion_detector_transaction);
	`uvm_object_utils(motion_detector_sequence)
	
	function new(string name ="motion_detector_sequence");
		super.new(name);
	endfunction
	
	task body();
		motion_detector_transaction tr;
		// pixel_diff == threshold, background_diff == variance
		tr = motion_detector_transaction::type_id::create("edge_case_1");
		tr.enable = 1;
		tr.curr_pixel = 150;
		tr.prev_pixel = 140;
		tr.threshold = 10; // pixel_diff == 10
		tr.background = 130; // background_diff == 20
		tr.variance = 20;
		start_item(tr); finish_item(tr);

		// Minimum pixel values
		tr = motion_detector_transaction::type_id::create("edge_case_2");
		tr.enable = 1;
		tr.curr_pixel = 0;
		tr.prev_pixel = 0;
		tr.background = 0;
		tr.threshold = 0;
		tr.variance = 2;
		start_item(tr); finish_item(tr);

		// Maximum pixel values
		tr = motion_detector_transaction::type_id::create("edge_case_3");
		tr.enable = 1;
		tr.curr_pixel = 255;
		tr.prev_pixel = 255;
		tr.background = 255;
		tr.threshold = 0;
		tr.variance = 255;
		start_item(tr); finish_item(tr);

		// Disable active
		tr = motion_detector_transaction::type_id::create("edge_case_4");
		tr.enable = 0;
		tr.curr_pixel = 100;
		tr.prev_pixel = 200;
		tr.background = 150;
		tr.threshold = 10;
		tr.variance = 20;
		start_item(tr); finish_item(tr);

		// pixel_diff < threshold, background_diff == variance
		tr = motion_detector_transaction::type_id::create("edge_case_5");
		tr.enable = 1;
		tr.curr_pixel = 100;
		tr.prev_pixel = 98; // diff = 2
		tr.threshold = 3; // no motion
		tr.background = 80; // diff = 20
		tr.variance = 20;
		start_item(tr); finish_item(tr);

		// pixel_diff > threshold, background_diff < variance
		tr = motion_detector_transaction::type_id::create("edge_case_6");
		tr.enable = 1;
		tr.curr_pixel = 200;
		tr.prev_pixel = 100; // diff = 100
		tr.threshold = 50;
		tr.background = 195; // diff = 5
		tr.variance = 10; // motion should be false
		start_item(tr); finish_item(tr);
		
		repeat(1000) begin
			tr = motion_detector_transaction::type_id::create("tr");
			start_item(tr);
			if (!tr.randomize() with {
			  enable        dist { 1 := 99, 0 := 1 };
			  curr_pixel    dist { [0:20] := 10, [21:235] := 80, [236:255] := 10 };
			  prev_pixel    dist { [0:20] := 10, [21:235] := 80, [236:255] := 10 };
			  background    dist { [0:20] := 5, [21:234] := 90, [235:255] := 5 };
			  variance      dist { [2:20] := 5, [21:234] := 90, [235:255] := 5 };
			}) begin
			  `uvm_warning("SEQUENCE", "Randomization failed!");
			end
			finish_item(tr);
		end
	endtask
endclass