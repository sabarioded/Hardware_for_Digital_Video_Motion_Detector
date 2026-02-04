/*------------------------------------------------------------------------------
 * File          : lm_sequence.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 26, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class lm_sequence extends uvm_sequence #(lm_trans);
	`uvm_object_utils(lm_sequence)
	
	function new(string name = "lm_sequence");
		super.new(name);
	endfunction
	
	virtual task body();
		lm_trans tr;
		
		repeat(10000) begin
			tr = lm_trans::type_id::create("tr");
			
			assert( tr.randomize() with {
					enable dist {1 := 99, 0 := 1};
					merge_valid dist {1 := 80, 0 := 20};
					merge_a dist {[0:5] := 10, [6:249] := 80, [250:255] := 10};
					merge_b dist {[0:5] := 10, [6:249] := 80, [250:255] := 10};
					resolve_valid dist {1 := 80, 0 := 20};
					resolve_label dist {[0:5] := 10, [6:249] := 80, [250:255] := 10};
					last_in_frame dist {1 := 10, 0 := 90};
					}) else begin
						`uvm_fatal(get_full_name(), "Randomization failed for labler_merger_trans")
					end
			start_item(tr);
			finish_item(tr);
			
		end
	endtask
endclass