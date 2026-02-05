/*------------------------------------------------------------------------------
 * File          : labler.sv
 * Project       : Hardware_for_Digital_Video_Motion_Detector
 * Author        : eposmk
 * Creation date : May 12, 2025
 * Description   : 1st-Pass Connected Component Labeler.
 *                 Assigns labels based on Left and Top neighbors.
 *------------------------------------------------------------------------------*/

module labeler #(
    parameter LABEL_WIDTH = 8
)(
    input  logic                   clk,
    input  logic                   rst,
    input  logic                   enable,
    input  logic                   last_in_frame,
    input  logic                   motion_pixel,
    input  logic [LABEL_WIDTH-1:0] left_label,
    input  logic [LABEL_WIDTH-1:0] top_label,

    output logic                   new_label_valid, // Request new label
    output logic [LABEL_WIDTH-1:0] new_label_value,

    output logic                   merge_labels,    // Request merge
    output logic [LABEL_WIDTH-1:0] merge_a,         // Target
    output logic [LABEL_WIDTH-1:0] merge_b,         // Source

    output logic [LABEL_WIDTH-1:0] current_label    // Assigned label
);

    // -------------------------------------------------------------------------
    // Next Label Counter
    // -------------------------------------------------------------------------
    logic [LABEL_WIDTH-1:0] next_label;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            next_label <= 1; // Start labeling from 1
        end else if (enable) begin
            if (last_in_frame) begin
                next_label <= 1;
            end else if (motion_pixel && new_label_valid && next_label != 0) begin
                next_label <= next_label + 1;
            end
        end
    end

    // -------------------------------------------------------------------------
    // Label Logic
    // -------------------------------------------------------------------------
    always_comb begin
        current_label   = 0;
        new_label_valid = 0;
        new_label_value = 0;
        merge_labels    = 0;
        merge_a         = 0;
        merge_b         = 0;

        if (!rst && enable && motion_pixel) begin
            if (left_label == 0 && top_label == 0) begin
                // Case 1: New isolated pixel -> Create new label
                new_label_valid = 1;
                new_label_value = next_label;
                current_label   = next_label;
            end else if (left_label != 0 && top_label == 0) begin
                // Case 2: Only Left neighbor -> Inherit Left
                current_label = left_label;
            end else if (left_label == 0 && top_label != 0) begin
                // Case 3: Only Top neighbor -> Inherit Top
                current_label = top_label;
            end else begin
                // Case 4: Both neighbors exist -> Resolve conflicts
                if (left_label < top_label) begin
                    current_label = left_label;
                    merge_labels  = 1;
                    merge_a       = left_label;
                    merge_b       = top_label;
                end else if (top_label < left_label) begin
                    current_label = top_label;
                    merge_labels  = 1;
                    merge_a       = top_label;
                    merge_b       = left_label;
                end else begin
                    current_label = left_label; // Neighbors match
                end
            end
        end
    end

    `ifndef SYNTHESIS
    `ifdef ENABLE_LABLER_ASSERTIONS

    // -------------------------------------------------------------------------
    // Assertions
    // -------------------------------------------------------------------------

    // [1] New label creation
    property new_label_isolated;
        @(posedge clk) disable iff (rst)
        (enable && motion_pixel && left_label==0 && top_label==0)
        |-> (new_label_valid && new_label_value==next_label && current_label==next_label && !merge_labels);
    endproperty
    assert property(new_label_isolated)
    else $fatal(1, $sformatf("[%0t] new_label_isolated: failed to create a new label", $time));

    // [2] No spurious new labels
    property no_new_label_when_neighbor_present;
        @(posedge clk) disable iff (rst)
        (enable && motion_pixel && (left_label!=0 || top_label!=0))
        |-> (!new_label_valid);
    endproperty
    assert property(no_new_label_when_neighbor_present)
    else $fatal(1, $sformatf("[%0t] no_new_label: incorrectly allocated new label", $time));

    // [3] Merge: Top is smaller
    property merge_two_neighbors_top_is_smaller;
        @(posedge clk) disable iff (rst)
        (enable && motion_pixel && left_label!=0 && top_label!=0 && top_label<left_label)
        |-> (current_label==top_label && merge_labels && merge_a==top_label && merge_b==left_label);
    endproperty
    assert property(merge_two_neighbors_top_is_smaller)
    else $fatal(1, $sformatf("[%0t] merge_two_neighbors_top_is_smaller failed", $time));

    // [4] Merge: Left is smaller
    property merge_two_neighbors_left_is_smaller;
        @(posedge clk) disable iff (rst)
        (enable && motion_pixel && left_label!=0 && top_label!=0 && left_label<top_label)
        |-> (current_label==left_label && merge_labels && merge_a==left_label && merge_b==top_label);
    endproperty
    assert property(merge_two_neighbors_left_is_smaller)
    else $fatal(1, $sformatf("[%0t] merge_two_neighbors_left_is_smaller failed", $time));

    // [5] No merge if equal
    property no_merge_when_neighbors_equal;
        @(posedge clk) disable iff (rst)
        (enable && motion_pixel && left_label!=0 && top_label!=0 && left_label==top_label)
        |-> (!merge_labels && current_label==left_label);
    endproperty
    assert property(no_merge_when_neighbors_equal)
    else $fatal(1, $sformatf("[%0t] no_merge_when_neighbors_equal failed", $time));

    // [6] Idle outputs
    property idle_outputs_when_disabled;
        @(posedge clk) disable iff (rst)
        ((!enable) || (!motion_pixel))
        |-> (!new_label_valid && !merge_labels &&
             current_label==0 && new_label_value==0 &&
             merge_a==0 && merge_b==0);
    endproperty
    assert property(idle_outputs_when_disabled)
    else $fatal(1, $sformatf("[%0t] idle_outputs_when_disabled failed", $time));

    // [7] Counter increments
    property next_label_increments_on_new_label;
        @(posedge clk) disable iff (rst)
        (enable && motion_pixel && new_label_valid && next_label!=0 && !last_in_frame)
        |=> (next_label==$past(next_label)+1);
    endproperty
    assert property(next_label_increments_on_new_label)
    else $fatal(1, $sformatf("[%0t] next_label_increments_on_new_label failed", $time));

    // [8] Counter reset at frame end
    property next_label_resets_on_frame_end;
        @(posedge clk) disable iff (rst)
        (enable && last_in_frame) |=> (next_label==1);
    endproperty
    assert property(next_label_resets_on_frame_end)
    else $fatal(1, $sformatf("[%0t] next_label_resets_on_frame_end failed", $time));

    // [9] Counter reset at system reset
    property next_label_resets_on_rst;
        @(posedge clk) disable iff (!rst)
        rst |=> next_label==1;
    endproperty
    assert property(next_label_resets_on_rst)
    else $fatal(1, $sformatf("[%0t] next_label_resets_on_rst failed", $time));

    `endif // ENABLE_LABLER_ASSERTIONS
    `endif // SYNTHESIS

endmodule
