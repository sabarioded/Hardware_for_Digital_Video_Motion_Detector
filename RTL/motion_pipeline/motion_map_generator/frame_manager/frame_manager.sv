/*------------------------------------------------------------------------------
 * File         : frame_manager.sv
 * Project      : RTL
 * Author       : eposmk
 * Creation date: May 10, 2025
 * Description  : Frame manager with grayscale conversion, 2-frame buffer rotation,
 *                and sigma-delta integration, plus inline assertions
 *------------------------------------------------------------------------------*/

module frame_manager (
  input  logic         clk,
  input  logic         rst,
  input  logic         enable,

  // AXI STREAM input pixel: {R[7:0], G[7:0], B[7:0], X[7:0]}
  input  logic [31:0]  pixel,
  input  logic         last_in_frame,

  // Outputs: current grayscale and previous frame pixel
  output logic [7:0]   curr_pixel,
  output logic [7:0]   prev_pixel,

  // sigma-delta interface
  input  logic         wr_background,
  output logic [7:0]   background_next,
  output logic [7:0]   variance_next
);

  localparam int FRAME_SIZE = 1280 * 720;

  // --------------------------------------------------
  // Internal storage and signals
  // --------------------------------------------------
  logic [7:0] frame_buff   [0:FRAME_SIZE-1];
  logic [7:0] background_buffer [0:FRAME_SIZE-1];
  logic [7:0] variance_buffer   [0:FRAME_SIZE-1];
  logic [$clog2(FRAME_SIZE)-1:0] rd_addr, wr_addr;
  logic [7:0] wr_buff;
  logic [15:0] gray_pixel;
  logic [7:0] background, variance;

  // --------------------------------------------------
  // Grayscale conversion (8-bit result in upper byte)
  // --------------------------------------------------
  always_comb begin
	gray_pixel = pixel[31:24]*8'd77 + pixel[23:16]*8'd150 + pixel[15:8]*8'd29;
  end

  // --------------------------------------------------
  // Stage N: Read prev and update curr_pixel, prev_pixel, wr_buff, rd_addr
  // --------------------------------------------------
  always_ff @(posedge clk or posedge rst) begin
	if (rst) begin
	  rd_addr    <= '0;
	  curr_pixel <= 8'd0;
	  prev_pixel <= 8'd0;
	  wr_buff    <= 8'd0;
	end else if (enable) begin
	  curr_pixel <= gray_pixel[15:8];
	  prev_pixel <= frame_buff[rd_addr];
	  wr_buff    <= gray_pixel[15:8];
	  rd_addr    <= last_in_frame ? '0 : rd_addr + 1;
	end
  end

  // --------------------------------------------------
  // Stage N+1: Write to frame buffer and rotate wr_addr
  // --------------------------------------------------
  always_ff @(posedge clk or posedge rst) begin
	if (rst) begin
	  wr_addr <= '0;
	  `ifndef SYNTHESIS
	  for (int i = 0; i < FRAME_SIZE; i++) begin
		frame_buff[i]      <= 8'd0;
		background_buffer[i] <= 8'd0;
		variance_buffer[i]   <= 8'd2;
	  end
	  `endif // SYNTHESIS
	end else if (enable) begin
	  frame_buff[wr_addr]       <= wr_buff;
	  // integrate sigma-delta outputs into buffers
	  background_buffer[wr_addr] <= background_next;
	  variance_buffer[wr_addr]   <= variance_next;
	  wr_addr <= rd_addr;
	end
  end

  // --------------------------------------------------
  // Combinational read of sigma-delta inputs
  // --------------------------------------------------
  always_comb begin
	background = background_buffer[rd_addr];
	variance   = variance_buffer[rd_addr];
  end

  // --------------------------------------------------
  // Sigma-Delta instance
  // --------------------------------------------------
  sigma_delta sd_inst (
	.clk           (clk),
	.rst           (rst),
	.enable        (enable),
	.wr_background (wr_background),
	.curr_pixel    (gray_pixel[15:8]),
	.background    (background),
	.variance      (variance),
	.background_next(background_next),
	.variance_next (variance_next)
  );

  `ifndef SYNTHESIS
  `ifdef ENABLE_FM_ASSERTIONS

	// -----------------------------------------
	// [1] Reset sanity: rd_addr/wr_addr/curr/prev cleared
	// -----------------------------------------
	always @(posedge clk) begin
	  if (rst) begin
		#1;
		assert (rd_addr == 0 && wr_addr == 0)
		  else `uvm_fatal("FM_A1",
			$sformatf("[%0t] FM_A1: rd_addr=%0d wr_addr=%0d not reset to zero",
					  $time, rd_addr, wr_addr));
		assert (curr_pixel == 0 && prev_pixel == 0)
		  else `uvm_fatal("FM_A2",
			$sformatf("[%0t] FM_A2: curr_pixel=%0d prev_pixel=%0d not reset to zero",
					  $time, curr_pixel, prev_pixel));
	  end
	end

	// -----------------------------------------
	// [2] Enable gating: when disabled, no state change
	// -----------------------------------------
	always @(posedge clk) begin
	  if (!rst && !enable) begin
		#1;
		assert ($stable(rd_addr) && $stable(wr_addr) &&
				$stable(curr_pixel) && $stable(prev_pixel))
		  else `uvm_fatal("FM_A_EN",
			$sformatf("[%0t] FM_A_EN: State changed while enable=0", $time));
	  end
	end

	// -----------------------------------------
	// [3] Grayscale conversion correctness
	// (Uses Y = 0.299R + 0.587G + 0.114B ? scaled)
	// -----------------------------------------
	logic [15:0] expected_gray;
	always_comb begin
	  expected_gray = pixel[31:24]*8'd77 + pixel[23:16]*8'd150 + pixel[15:8]*8'd29;
	end

	always @(posedge clk) begin
	  if (!rst && enable) begin
		#1;
		assert (curr_pixel == $past(expected_gray[15:8]))
		  else `uvm_fatal("FM_A3",
			$sformatf("[%0t] FM_A3: curr_pixel=%0d expected_gray=%0d",
					  $time, curr_pixel, $past(expected_gray[15:8])));
	  end
	end

	// -----------------------------------------
	// [4] prev_pixel matches previous frame buffer content
	// -----------------------------------------
	always @(posedge clk) begin
	  if (!rst && enable) begin
		#1;
		assert (prev_pixel == frame_buff[$past(rd_addr)])
		  else `uvm_fatal("FM_A4",
			$sformatf("[%0t] FM_A4: prev_pixel=%0d expected frame_buff[%0d]=%0d",
					  $time, prev_pixel, $past(rd_addr), frame_buff[$past(rd_addr)]));
	  end
	end

	// -----------------------------------------
	// [5] wr_addr must always equal the previous rd_addr when enabled
	// -----------------------------------------
	always @(posedge clk) begin
	  if (!rst && enable) begin
		#1;
		assert (wr_addr == $past(rd_addr))
		  else `uvm_fatal("FM_A5",
			$sformatf("[%0t] FM_A5: wr_addr=%0d expected=%0d",
					  $time, wr_addr, $past(rd_addr)));
	  end
	end

	// -----------------------------------------
	// [6] Frame buffer write matches wr_buff
	// -----------------------------------------
	always @(posedge clk) begin
	  if (!rst && enable) begin
		#1;
		assert (frame_buff[$past(wr_addr)] == $past(wr_buff))
		  else `uvm_fatal("FM_A6",
			$sformatf("[%0t] FM_A6: frame_buff[%0d]=%0d expected wr_buff=%0d",
					  $time, $past(wr_addr), frame_buff[$past(wr_addr)], $past(wr_buff)));
	  end
	end

	// -----------------------------------------
	// [7] Frame boundary: rd_addr must reset at last_in_frame
	// -----------------------------------------
	always @(posedge clk) begin
	  if (!rst && enable && last_in_frame) begin
		#1;
		assert (rd_addr == 0)
		  else `uvm_fatal("FM_A7",
			$sformatf("[%0t] FM_A7: rd_addr=%0d not reset at frame boundary",
					  $time, rd_addr));
	  end
	end

	// -----------------------------------------
	// [8] rd_addr/wr_addr wrap-around must stay within valid FRAME_SIZE
	// -----------------------------------------
	always @(posedge clk) begin
	  if (!rst && enable) begin
		#1;
		assert (rd_addr < FRAME_SIZE && wr_addr < FRAME_SIZE)
		  else `uvm_fatal("FM_A8",
			$sformatf("[%0t] FM_A8: Address out of bounds rd=%0d wr=%0d FRAME_SIZE=%0d",
					  $time, rd_addr, wr_addr, FRAME_SIZE));
	  end
	end

	// -----------------------------------------
	// [9] Background/variance integration sanity
	// The buffers must always be updated with background_next/variance_next
	// -----------------------------------------
	always @(posedge clk) begin
	  if (!rst && enable) begin
		#1;
		assert (background_buffer[$past(wr_addr)] == $past(background_next))
		  else `uvm_fatal("FM_A9_BG",
			$sformatf("[%0t] FM_A9: background_buffer[%0d]=%0d expected=%0d",
					  $time, $past(wr_addr),
					  background_buffer[$past(wr_addr)], $past(background_next)));

		assert (variance_buffer[$past(wr_addr)] == $past(variance_next))
		  else `uvm_fatal("FM_A9_VAR",
			$sformatf("[%0t] FM_A9: variance_buffer[%0d]=%0d expected=%0d",
					  $time, $past(wr_addr),
					  variance_buffer[$past(wr_addr)], $past(variance_next)));
	  end
	end

	// -----------------------------------------
	// [10] When not enable, background_next and variance_next are stable
	// -----------------------------------------
	always @(posedge clk) begin
	  if (!rst && !enable) begin
		#1;
		assert ($stable(background_next) && $stable(variance_next))
		  else `uvm_fatal("FM_A10",
			$sformatf("[%0t] FM_A10: background_next/variance_next changed while enable=0", $time));
	  end
	end

  `endif // ENABLE_FM_ASSERTIONS
  `endif // SYNTHESIS



endmodule: frame_manager