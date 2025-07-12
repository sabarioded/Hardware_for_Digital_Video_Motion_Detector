/*------------------------------------------------------------------------------
 * File          : label_merger.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 12, 2025
 * Description   :
 *------------------------------------------------------------------------------*/
module label_merger #(
	parameter LABEL_WIDTH = 8,  // Supports up to 256 labels
	parameter MAX_PATH_DEPTH = 4
)(
	input  logic                     clk,
	input  logic                     rst,
	input  logic					enable,
	input  logic 					last_in_frame,

	// Merge interface from labeler
	input  logic                     merge_valid,
	input  logic [LABEL_WIDTH-1:0]  merge_a,
	input  logic [LABEL_WIDTH-1:0]  merge_b,

	// Label to resolve (from labeler or bbox_tracker)
	input  logic                     resolve_valid,
	input  logic [LABEL_WIDTH-1:0]  resolve_label,
	output logic [LABEL_WIDTH-1:0]  resolved_label
);
localparam NUM_LABELS  = 1 << LABEL_WIDTH;

// Lookup table: label_table[i] gives the parent label of i
logic [LABEL_WIDTH-1:0] label_table[NUM_LABELS];

// Intermediate wires for parallel path compression for RESOLVE path
// The size of this array depends on MAX_PATH_DEPTH
logic [LABEL_WIDTH-1:0] resolve_parents [MAX_PATH_DEPTH];

// Intermediate wires for parallel root finding for MERGE path
// The size of these arrays depends on MAX_PATH_DEPTH
logic [LABEL_WIDTH-1:0] merge_a_roots [MAX_PATH_DEPTH];
logic [LABEL_WIDTH-1:0] merge_b_roots [MAX_PATH_DEPTH];
logic [LABEL_WIDTH-1:0] final_root_a, final_root_b;

genvar k;
generate
	// Root finding logic for MERGE path with configurable MAX_PATH_DEPTH
	// Initial lookup for the direct parent
	assign merge_a_roots[0] = label_table[merge_a];
	assign merge_b_roots[0] = label_table[merge_b];

	// Generate subsequent lookups based on MAX_PATH_DEPTH
	for (k = 1; k < MAX_PATH_DEPTH; k++) begin : cascade_merge_lookups
		assign merge_a_roots[k] = label_table[merge_a_roots[k-1]];
		assign merge_b_roots[k] = label_table[merge_b_roots[k-1]];
	end
	// The 'final_root_a/b' is the last parent found in the chain.
	assign final_root_a = merge_a_roots[MAX_PATH_DEPTH-1];
	assign final_root_b = merge_b_roots[MAX_PATH_DEPTH-1];
endgenerate


integer i;
always_ff @(posedge clk or posedge rst) begin
	if (rst) begin
		for (i = 0; i < NUM_LABELS; i++) begin
			label_table[i] <= i; // Each label is its own parent initially
		end
	end else if (enable) begin
		if (last_in_frame) begin
			for (i = 0; i < NUM_LABELS; i++) begin
				label_table[i] <= i;
			end
		end

		if (merge_valid) begin
			label_table[merge_b] <= final_root_a;
		end
	end
end


genvar j;
generate
	assign resolve_parents[0] = label_table[resolve_label];

	for (j = 1; j < MAX_PATH_DEPTH; j++) begin : cascade_resolve_lookups
		assign resolve_parents[j] = label_table[resolve_parents[j-1]];
	end
endgenerate

// Output `resolved_label` (combinational)
always_comb begin
	if (!rst && enable && resolve_valid) begin
		resolved_label = resolve_parents[MAX_PATH_DEPTH-1];
	end else begin
		resolved_label = 0;
	end
end


	`ifndef SYNTHESIS
	`ifdef ENABLE_LM_ASSERTIONS

	`endif // ENABLE_MMG_ASSERTIONS
	`endif // SYNTHESIS

endmodule