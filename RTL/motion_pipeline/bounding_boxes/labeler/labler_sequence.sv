//------------------------------------------------------------------------------
// File          : labler_sequence.sv
// Project       : Project_RTL
// Author        : eposmk
// Creation date : May 23, 2025
// Description   : UVM sequence for labler transaction
//------------------------------------------------------------------------------

class labler_sequence extends uvm_sequence#(labler_trans);
  `uvm_object_utils(labler_sequence)

  // Constructor with proper types for name and parent
  function new(string name = "labler_sequence");
	super.new(name);
  endfunction: new

  // Sequence body
  virtual task body();
	labler_trans tr;

	repeat (10000) begin
	  // Create transaction under the sequencer (a uvm_component)
	  tr = labler_trans::type_id::create(
			 $sformatf("%s_tran", get_name()),
			 m_sequencer
		   );

	  // Randomize fields with weighted distributions
	  assert(tr.randomize() with {
		enable        dist {1 := 95, 0 := 5};
		motion_pixel  dist {1 := 60, 0 := 40};
		last_in_frame  dist {1 := 10, 0 := 90};
		left_label    dist {255 := 5, 0 := 35, [1:85] := 20, [86:170] := 20, [171:254] := 20};
		top_label     dist {255 := 5, 0 := 35, [1:85] := 20, [86:170] := 20, [171:254] := 20};
	  }) else begin
		`uvm_error(get_full_name(), "Randomization failed for labler_trans")
	  end

	  // Start and finish sequence item
	  start_item(tr);
	  finish_item(tr);
	end
	
	repeat (1000) begin
		// Create transaction under the sequencer (a uvm_component)
		tr = labler_trans::type_id::create(
			   $sformatf("%s_tran", get_name()),
			   m_sequencer
			 );

		// Randomize fields with weighted distributions
		assert(tr.randomize() with {
		  enable        == 1;
		  motion_pixel  dist {1 := 80, 0 := 20};
		  left_label    == 0;
		  top_label     == 0;
		}) else begin
		  `uvm_error(get_full_name(), "Randomization failed for labler_trans")
		end

		// Start and finish sequence item
		start_item(tr);
		finish_item(tr);
	end
	
	repeat (10) begin
		// Create transaction under the sequencer (a uvm_component)
		tr = labler_trans::type_id::create(
			   $sformatf("%s_tran", get_name()),
			   m_sequencer
			 );

		// Randomize fields with weighted distributions
		assert(tr.randomize() with {
		  enable        == 1;
		  motion_pixel  dist {1 := 80, 0 := 20};
		  left_label    == 255;
		  top_label     == 255;
		}) else begin
		  `uvm_error(get_full_name(), "Randomization failed for labler_trans")
		end

		// Start and finish sequence item
		start_item(tr);
		finish_item(tr);
	end
	
	repeat (10) begin
		// Create transaction under the sequencer (a uvm_component)
		tr = labler_trans::type_id::create(
			   $sformatf("%s_tran", get_name()),
			   m_sequencer
			 );

		// Randomize fields with weighted distributions
		assert(tr.randomize() with {
		  enable        == 1;
		  motion_pixel  dist {1 := 80, 0 := 20};
		  left_label    == 0;
		  top_label     == 255;
		}) else begin
		  `uvm_error(get_full_name(), "Randomization failed for labler_trans")
		end

		// Start and finish sequence item
		start_item(tr);
		finish_item(tr);
	end
	
	repeat (10) begin
		// Create transaction under the sequencer (a uvm_component)
		tr = labler_trans::type_id::create(
			   $sformatf("%s_tran", get_name()),
			   m_sequencer
			 );

		// Randomize fields with weighted distributions
		assert(tr.randomize() with {
		  enable        == 1;
		  motion_pixel  dist {1 := 80, 0 := 20};
		  left_label    == 255;
		  top_label     == 0;
		}) else begin
		  `uvm_error(get_full_name(), "Randomization failed for labler_trans")
		end

		// Start and finish sequence item
		start_item(tr);
		finish_item(tr);
	end
	
  endtask: body

endclass: labler_sequence