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
	  for (int i = 0; i < FRAME_SIZE; i++) begin
		frame_buff[i]      <= 8'd0;
		background_buffer[i] <= 8'd0;
		variance_buffer[i]   <= 8'd2;
	  end
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

  // --------------------------------------------------
  // Assertions (excluded from synthesis)
  // --------------------------------------------------
  `ifndef SYNTHESIS
  `ifdef ENABLE_FM_ASSERTIONS
	// [1] After reset, rd_addr and wr_addr should be 0
	always @(posedge clk) begin
	  if (rst) begin
		#1;
		assert (rd_addr == 0 && wr_addr == 0)
		  else $error("[%0t] A1: Addresses not reset to zero", $time);
	  end
	end

	// [2] After reset, curr_pixel and prev_pixel should be 0
	always @(posedge clk) begin
	  if (rst) begin
		#1;
		assert (curr_pixel == 8'd0 && prev_pixel == 8'd0)
		  else $error("[%0t] A2: Pixels not reset to zero", $time);
	  end
	end

	// [3] curr_pixel matches grayscale conversion of prior input
	always @(posedge clk) begin
	  if (!rst && enable) begin
		#1;
		assert (curr_pixel == $past(gray_pixel[15:8]))
		  else $error("[%0t] A3: curr_pixel mismatch", $time);
	  end
	end

	// [4] prev_pixel matches frame buffer content
	always @(posedge clk) begin
	  if (!rst && enable) begin
		#1;
		assert (prev_pixel == frame_buff[$past(rd_addr)])
		  else $error("[%0t] A4: prev_pixel mismatch", $time);
	  end
	end

	// [5] wr_addr should equal rd_addr when enabled
	always @(posedge clk) begin
	  if (!rst && enable) begin
		#1;
		assert (wr_addr == $past(rd_addr))
		  else $error("[%0t] A5: wr_addr != rd_addr", $time);
	  end
	end

	// [6] Frame buffer write correctness
	always @(posedge clk) begin
	  if (!rst && enable) begin
		#1;
		assert (frame_buff[$past(wr_addr)] == $past(wr_buff))
		  else $error("[%0t] A6: frame buffer write mismatch", $time);
	  end
	end

	// [7] rd_addr reset on last_in_frame
	always @(posedge clk) begin
	  if (!rst && enable && last_in_frame) begin
		#1;
		assert (rd_addr == 0)
		  else $error("[%0t] A7: rd_addr not reset on last_in_frame", $time);
	  end
	end

	// [8] Sigma-Delta integration: buffers reflect output
	always @(posedge clk) begin
	  if (!rst && enable) begin
		#1;
		assert (background == background_buffer[rd_addr] && variance == variance_buffer[rd_addr])
		  else $error("[%0t] A8: Sigma-delta buffer mismatch", $time);
	  end
	end
  `endif // ENABLE_FM_ASSERTIONS
  `endif // SYNTHESIS

endmodule: frame_manager