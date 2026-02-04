
class mp_scoreboard extends uvm_component;
	`uvm_component_utils(mp_scoreboard)

	uvm_analysis_imp#(mp_trans, mp_scoreboard) ap;

	localparam HIGHLIGHT_COLOR = 32'hFF000000;
	localparam int WIDTH = 352;
	localparam int HEIGHT = 288;
	localparam int DEPTH = WIDTH*HEIGHT;
	
	logic [31:0] output_pixel [0:DEPTH-1]; // DUT's output for current frame

	int unsigned x;
	int unsigned y;
	string dump_name;
	int    dump_fd;
	int idx;

	
	function new(string name, uvm_component parent = null);
	  super.new(name, parent);
	endfunction

	virtual function void build_phase(uvm_phase phase);
	  super.build_phase(phase);
	  x = 0;
	  y = 0;
	  ap = new("ap", this);
	endfunction

	virtual function void write(mp_trans tr);
	  int idx = y * tr.width + x;
	  
	  output_pixel[idx] = tr.highlighted_pixel;
	  
	  // Advance counters and handle end-of-frame logic
	  if (tr.last_in_frame) begin	
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
		  end
		  $fclose(dump_fd);
		  `uvm_info("MP_SCB", $sformatf("Dumped DUT output to %s", dump_name), UVM_LOW);
		  x = 0;
		  y = 0;
	  end else if(x == tr.width-1) begin
		  x = 0;
		  y = y+1;
		end else begin
		  x = x+1;
		end
	  
	endfunction



  endclass: mp_scoreboard