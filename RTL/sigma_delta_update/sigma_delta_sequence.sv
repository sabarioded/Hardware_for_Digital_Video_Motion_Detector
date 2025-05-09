/*------------------------------------------------------------------------------
 * File          : sigma_delta_sequence.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 5, 2025
 * Description   :
 *------------------------------------------------------------------------------*/
class sigma_delta_sequence extends uvm_sequence #(sigma_delta_transaction);
	`uvm_object_utils(sigma_delta_sequence)

	function new(string name = "sigma_delta_sequence");
	  super.new(name);
	endfunction

	task body();
	  sigma_delta_transaction tr;

	  // === Edge Case 1: Overflow ===
	  `uvm_info("SEQUENCE", "Running overflow test", UVM_MEDIUM);
	  tr = sigma_delta_transaction::type_id::create("tr");
	  start_item(tr);
	  tr.enable = 1;
	  tr.wr_background = 0;
	  tr.curr_pixel = 255;
	  tr.background = 255;
	  tr.variance = 255;
	  finish_item(tr);

	  // === Edge Case 2: Underflow ===
	  `uvm_info("SEQUENCE", "Running underflow test", UVM_MEDIUM);
	  tr = sigma_delta_transaction::type_id::create("tr");
	  start_item(tr);
	  tr.enable = 1;
	  tr.wr_background = 0;
	  tr.curr_pixel = 0;
	  tr.background = 0;
	  tr.variance = 2;
	  finish_item(tr);

	  // === Randomized Stimulus ===
	  repeat (1000) begin
		tr = sigma_delta_transaction::type_id::create("tr");
		start_item(tr);
		if (!tr.randomize() with {
		  enable        dist { 1 := 99, 0 := 1 };
		  wr_background dist { 1 := 5, 0 := 95 };
		  curr_pixel    dist { [0:20] := 10, [21:235] := 80, [236:255] := 10 };
		  background    dist { [0:10] := 5, [11:244] := 90, [245:255] := 5 };
		  variance      dist { [2:10] := 5, [11:244] := 90, [245:255] := 5 };
		}) begin
		  `uvm_warning("SEQUENCE", "Randomization failed!");
		end
		finish_item(tr);
	  end
	endtask
  endclass


