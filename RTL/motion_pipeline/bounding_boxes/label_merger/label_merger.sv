/*------------------------------------------------------------------------------
 * File          : label_merger.sv
 * Project       : Hardware_for_Digital_Video_Motion_Detector
 * Author        : eposmk
 * Creation date : May 12, 2025
 * Description   : Disjoint-set union merger for Connected Component Labeling.
 *------------------------------------------------------------------------------*/

module label_merger #(
    parameter LABEL_WIDTH    = 8,
    parameter MAX_PATH_DEPTH = 4
)(
    input  logic                     clk,
    input  logic                     rst,
    input  logic                     enable,
    input  logic                     last_in_frame,

    // Merge interface (from labeler)
    input  logic                     merge_valid,
    input  logic [LABEL_WIDTH-1:0]   merge_a,
    input  logic [LABEL_WIDTH-1:0]   merge_b,

    // Resolve interface (get final root)
    input  logic                     resolve_valid,
    input  logic [LABEL_WIDTH-1:0]   resolve_label,
    output logic [LABEL_WIDTH-1:0]   resolved_label
);

    localparam NUM_LABELS = 1 << LABEL_WIDTH;

    // -------------------------------------------------------------------------
    // Internal Tables & Signals
    // -------------------------------------------------------------------------
    logic [LABEL_WIDTH-1:0] label_table[NUM_LABELS];

    // Parallel path compression wires
    logic [LABEL_WIDTH-1:0] resolve_parents [MAX_PATH_DEPTH];
    logic [LABEL_WIDTH-1:0] merge_a_roots   [MAX_PATH_DEPTH];
    logic [LABEL_WIDTH-1:0] merge_b_roots   [MAX_PATH_DEPTH];
    logic [LABEL_WIDTH-1:0] final_root_a, final_root_b;

    // -------------------------------------------------------------------------
    // Root Finding Logic (Merge Path)
    // -------------------------------------------------------------------------
    genvar k;
    generate
        assign merge_a_roots[0] = label_table[merge_a];
        assign merge_b_roots[0] = label_table[merge_b];

        for (k = 1; k < MAX_PATH_DEPTH; k++) begin : cascade_merge_lookups
            assign merge_a_roots[k] = label_table[merge_a_roots[k-1]];
            assign merge_b_roots[k] = label_table[merge_b_roots[k-1]];
        end

        assign final_root_a = merge_a_roots[MAX_PATH_DEPTH-1];
        assign final_root_b = merge_b_roots[MAX_PATH_DEPTH-1];
    endgenerate

    // -------------------------------------------------------------------------
    // Table Update
    // -------------------------------------------------------------------------
    integer i;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            for (i = 0; i < NUM_LABELS; i++) begin
                label_table[i] <= i; // Initialize identity
            end
        end else if (enable) begin
            if (last_in_frame) begin
                for (i = 0; i < NUM_LABELS; i++) begin
                    label_table[i] <= i; // Reset frame
                end
            end

            if (merge_valid) begin
                label_table[merge_b] <= final_root_a; // Union operation
            end
        end
    end

    // -------------------------------------------------------------------------
    // Root Finding Logic (Resolve Path)
    // -------------------------------------------------------------------------
    genvar j;
    generate
        assign resolve_parents[0] = label_table[resolve_label];

        for (j = 1; j < MAX_PATH_DEPTH; j++) begin : cascade_resolve_lookups
            assign resolve_parents[j] = label_table[resolve_parents[j-1]];
        end
    endgenerate

    always_comb begin
        if (!rst && enable && resolve_valid) begin
            resolved_label = resolve_parents[MAX_PATH_DEPTH-1];
        end else begin
            resolved_label = 0;
        end
    end

    `ifndef SYNTHESIS
    `ifdef ENABLE_LM_ASSERTIONS

    // -------------------------------------------------------------------------
    // Assertions
    // -------------------------------------------------------------------------

    // [1] Reset / Frame-End Identity Table Checks
    always @(posedge clk) begin
        if (rst) begin
            @(posedge clk);
            foreach (label_table[i]) begin
                if (label_table[i] !== i) begin
                    `uvm_fatal("LM_A1", $sformatf("[%0t] LM_A1: label_table[%0d] = %0d, expected %0d", $time, i, label_table[i], i))
                end
            end
        end
    end

    // [2] Merge Interface Sanity Checks
    property merge_inputs_in_range;
        @(posedge clk) disable iff (rst)
        (enable && merge_valid) |-> ((merge_a < NUM_LABELS) && (merge_b < NUM_LABELS));
    endproperty
    assert property (merge_inputs_in_range)
    else `uvm_fatal("LM_A2", $sformatf("[%0t] LM_A3: merge_a=%0d or merge_b=%0d out of range", $time, merge_a, merge_b));

    // [3] Merge Operation Behavior
    property merge_updates_to_final_root;
        @(posedge clk) disable iff (rst)
        (enable && merge_valid) |=> (label_table[$past(merge_b)] == $past(final_root_a));
    endproperty
    assert property (merge_updates_to_final_root)
    else `uvm_fatal("LM_A3", $sformatf("[%0t] LM_A4: label_table[%0d]=%0d != expected final_root_a=%0d",
                                      $time, $past(merge_b), label_table[$past(merge_b)], $past(final_root_a)));

    // [4] Resolve Path Behavior
    property resolve_must_return_root;
        @(posedge clk) disable iff (rst)
        (enable && resolve_valid) |-> (resolved_label == label_table[resolved_label]);
    endproperty
    assert property (resolve_must_return_root)
    else `uvm_fatal("LM_A4", $sformatf("[%0t] LM_A5: resolved_label=%0d not a root!", $time, resolved_label));

    property resolve_output_in_range;
        @(posedge clk) disable iff (rst)
        (enable && resolve_valid) |-> ((resolved_label < NUM_LABELS));
    endproperty
    assert property (resolve_output_in_range)
    else `uvm_fatal("LM_A5", $sformatf("[%0t] LM_A6: resolved_label=%0d invalid/out-of-range", $time, resolved_label));

    // [5] Protocol & Idle Checks
    property idle_resolve_must_be_zero;
        @(posedge clk) disable iff (rst)
        ((!enable) || (!resolve_valid)) |-> (resolved_label == 0);
    endproperty
    assert property (idle_resolve_must_be_zero)
    else `uvm_fatal("LM_A6", $sformatf("[%0t] LM_A7: resolved_label not zero when idle", $time));

    `endif // ENABLE_LM_ASSERTIONS
    `endif // SYNTHESIS

endmodule
