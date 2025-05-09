/*------------------------------------------------------------------------------
 * File          : box_filter_sequence.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class box_filter_sequence extends uvm_sequence #(box_filter_transaction);
	`uvm_object_utils(box_filter_sequence)

	function new(string name = "box_filter_sequence");
		super.new(name);
	endfunction

	task body();
		box_filter_transaction tr;

		// === Edge Case 1: All zeros
		tr = box_filter_transaction::type_id::create("all_zero");
		tr.enable = 1;
		tr.motion_map = 9'b000000000;
		tr.neighbors_number = 4'd3;
		start_item(tr); finish_item(tr);

		// === Edge Case 2: All ones
		tr = box_filter_transaction::type_id::create("all_ones");
		tr.enable = 1;
		tr.motion_map = 9'b111111111;
		tr.neighbors_number = 4'd8;
		start_item(tr); finish_item(tr);

		// === Edge Case 3: Exactly threshold
		tr = box_filter_transaction::type_id::create("exact_thresh");
		tr.enable = 1;
		tr.motion_map = 9'b000111000; // 3 motion pixels
		tr.neighbors_number = 3; // should be false
		start_item(tr); finish_item(tr);

		// === Edge Case 4: Just over threshold
		tr = box_filter_transaction::type_id::create("above_thresh");
		tr.enable = 1;
		tr.motion_map = 9'b000111001; // 4 motion pixels
		tr.neighbors_number = 3; // should be true
		start_item(tr); finish_item(tr);

		// === Edge Case 5: Just under threshold
		tr = box_filter_transaction::type_id::create("below_thresh");
		tr.enable = 1;
		tr.motion_map = 9'b000110000; // 2 motion pixels
		tr.neighbors_number = 3; // should be false
		start_item(tr); finish_item(tr);

		// === Randomized tests
		repeat (1000) begin
			tr = box_filter_transaction::type_id::create("tr");
			start_item(tr);
			if (!tr.randomize() with {
				enable dist { 1 := 99, 0 := 1 };
				motion_map inside {[0:511]};
				neighbors_number inside {[0:8]};
			}) begin
				`uvm_warning("SEQUENCE", "Randomization failed!");
			end
			finish_item(tr);
		end
	endtask
endclass
