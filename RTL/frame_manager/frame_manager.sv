/*------------------------------------------------------------------------------
 * File          : frame_manager.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 10, 2025
 * Description   : Frame manager with grayscale conversion and 3-frame buffer rotation
 *------------------------------------------------------------------------------*/

module frame_manager (
	input  logic        clk,
	input  logic        rst,
	input  logic        enable,

	// AXI STREAM input
	input  logic        valid,
	input  logic [31:0] pixel,   // {R[7:0], G[7:0], B[7:0], X[7:0]}
	input  logic        last,

	// from control
	input  logic [10:0] width,
	input  logic [9:0]  height,

	output logic [7:0]  pixel_t1,
	output logic [7:0]  pixel_t2,
	output logic [7:0]  curr_pixel,

	// to AXI STREAM
	output logic        ready
);

	localparam FRAME_SIZE = 1280 * 720; // Max frame size

	typedef enum logic [1:0] {
		BUF0 = 2'd0,
		BUF1 = 2'd1,
		BUF2 = 2'd2
	} buf_id_t;

	logic [7:0] frame0 [0:FRAME_SIZE-1];
	logic [7:0] frame1 [0:FRAME_SIZE-1];
	logic [7:0] frame2 [0:FRAME_SIZE-1];

	buf_id_t write_buf, read_buf1, read_buf2;

	logic [18:0] wr_addr, rd_addr;
	logic [18:0] total_pixels;
	logic [7:0]  gray_pixel;

	assign ready = enable;

	// Grayscale conversion
	assign gray_pixel = (pixel[31:24] * 8'd77 + pixel[23:16] * 8'd150 + pixel[15:8] * 8'd29) >> 8;
	assign curr_pixel = gray_pixel;

	always_ff @(posedge clk or posedge rst) begin
		if (rst) begin
			wr_addr   <= 0;
			rd_addr   <= 0;
			total_pixels <= 0;
			write_buf <= BUF0;
			read_buf1 <= BUF1;
			read_buf2 <= BUF2;
		end else if (enable && valid) begin
			total_pixels <= width * height;
			
			case (write_buf)
				BUF0: frame0[wr_addr] <= gray_pixel;
				BUF1: frame1[wr_addr] <= gray_pixel;
				BUF2: frame2[wr_addr] <= gray_pixel;
			endcase

			wr_addr <= wr_addr + 1;

			if (last) begin
				wr_addr <= 0;
				// Rotate buffer roles
				write_buf <= read_buf1;
				read_buf1 <= read_buf2;
				read_buf2 <= write_buf;
				rd_addr <= 0;
			end
		end

		if (enable && rd_addr < total_pixels) begin
			case (read_buf1)
				BUF0: pixel_t1 <= frame0[rd_addr];
				BUF1: pixel_t1 <= frame1[rd_addr];
				BUF2: pixel_t1 <= frame2[rd_addr];
			endcase

			case (read_buf2)
				BUF0: pixel_t2 <= frame0[rd_addr];
				BUF1: pixel_t2 <= frame1[rd_addr];
				BUF2: pixel_t2 <= frame2[rd_addr];
			endcase

			rd_addr <= rd_addr + 1;
		end
	end

endmodule
