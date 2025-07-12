/*------------------------------------------------------------------------------
 * File        : addr_manager.sv
 * Project     : Project_RTL
 * Author      : eposmk
 * Creation date : Jul 5, 2025
 * Description :
 * This module manages memory addresses for a triple-buffered frame system.
 *------------------------------------------------------------------------------*/
module addr_manager (
	input  logic        clk,
	input  logic        rst,

	input  logic        enable,
	input  logic        last,

	output logic [31:0] write_addr,
	output logic [31:0] read_addr
);

	localparam BASE_ADDR       = 32'h0000_0000;
	localparam FRAME_SIZE_BYTES = 3_686_400;

	logic [1:0] write_idx;
	logic [1:0] read_idx;

	logic [1:0] next_write_idx;
	logic [1:0] next_read_idx;

	always_ff @(posedge clk or posedge rst) begin
		if (rst) begin
			write_idx  <= 0;
			read_idx   <= 2;
			write_addr <= BASE_ADDR;
			read_addr  <= BASE_ADDR + 2 * FRAME_SIZE_BYTES;
		end else begin
			next_write_idx = write_idx;
			next_read_idx  = read_idx;

			if (enable && last) begin
				next_write_idx = (write_idx + 1) % 3;
				next_read_idx  = (read_idx + 1) % 3;
			end

			write_idx <= next_write_idx;
			read_idx  <= next_read_idx;

			if (enable && last) begin
				write_addr <= BASE_ADDR + (next_write_idx * FRAME_SIZE_BYTES);
				read_addr  <= BASE_ADDR + (next_read_idx * FRAME_SIZE_BYTES);
			end else if (enable) begin
				write_addr <= write_addr + 4;
				read_addr  <= read_addr + 4;
			end
		end
	end

endmodule
