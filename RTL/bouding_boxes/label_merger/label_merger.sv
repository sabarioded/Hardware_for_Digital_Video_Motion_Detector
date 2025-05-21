/*------------------------------------------------------------------------------
 * File          : label_merger.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 12, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module label_merger #(
	parameter LABEL_WIDTH = 6,  // Supports up to 64 labels
	parameter NUM_LABELS  = 1 << LABEL_WIDTH
)(
	input  logic                     clk,
	input  logic                     rst,

	// Merge interface from labeler
	input  logic                     merge_valid,
	input  logic [LABEL_WIDTH-1:0]  merge_a,
	input  logic [LABEL_WIDTH-1:0]  merge_b,

	// Label to resolve (from labeler or bbox_tracker)
	input  logic                     resolve_valid,
	input  logic [LABEL_WIDTH-1:0]  resolve_label,
	output logic [LABEL_WIDTH-1:0]  resolved_label
);

	// Lookup table: label_table[i] gives the parent label of i
	logic [LABEL_WIDTH-1:0] label_table[NUM_LABELS];

	// Initialization
	integer i;
	always_ff @(posedge clk or posedge rst) begin
		if (rst) begin
			for (i = 0; i < NUM_LABELS; i++)
				label_table[i] <= i;  // self-parented
		end
	end

	// Union operation (merge two labels)
	always_ff @(posedge clk) begin
		if (merge_valid) begin
			label_table[merge_b] <= merge_a;  // Merge b into a
		end
	end

	// Path compression on read (flatten the tree and check who is the root)
	logic [LABEL_WIDTH-1:0] root_1, root_2;
	always_comb begin
		if(resolve_valid) begin
			root_1 = label_table[resolve_label];
			root_2 = label_table[root_1];
			resolved_label = (root_2 == root_1) ? root_1 : root_2;
		end
	end

endmodule
