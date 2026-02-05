/*------------------------------------------------------------------------------
 * File          : bbox_top.sv
 * Project       : Hardware_for_Digital_Video_Motion_Detector
 * Author        : eposmk
 * Creation date : May 12, 2025
 * Description   : Pipelined, ping-pong bounding box top module.
 *                 Manages labeling, merging, and bounding box aggregation banks.
 *------------------------------------------------------------------------------*/

module bbox_top #(
    parameter WIDTH_BITS      = 11,
    parameter HEIGHT_BITS     = 10,
    parameter LABEL_WIDTH     = 8,
    parameter NUM_LABELS      = 1 << LABEL_WIDTH,
    parameter MAX_WIDTH       = 1 << WIDTH_BITS,
    parameter HIGHLIGHT_COLOR = 32'hFF000000
)(
    input  logic                   clk,
    input  logic                   rst,
    input  logic                   enable,

    // Streaming input
    input  logic                   motion_pixel,
    input  logic                   last_in_frame,
    input  logic [31:0]            rgb_pixel,

    // Frame size
    input  logic [WIDTH_BITS-1:0]  width,
    input  logic [HEIGHT_BITS-1:0] height,

    // Bounding box outputs (streaming)
    output logic [31:0]            highlighted_pixel,
    output logic                   pixel_valid

    // DEBUG
    /*,
    output logic [WIDTH_BITS-1:0]  x_out,
    output logic [HEIGHT_BITS-1:0] y_out
    // END DEBUG
    */
);

    localparam int PROX = 5;

    // -------------------------------------------------------------------------
    // Coordinate Tracking
    // -------------------------------------------------------------------------
    logic [WIDTH_BITS-1:0]  x;
    logic [HEIGHT_BITS-1:0] y;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            x <= 0;
            y <= 0;
        end else if (enable) begin
            if (last_in_frame) begin
                x <= 0;
                y <= 0;
            end else if (x == width - 1) begin
                x <= 0;
                y <= y + 1;
            end else begin
                x <= x + 1;
            end
        end
    end

    // -------------------------------------------------------------------------
    // Stage 1: Labeler + Line Buffer
    // -------------------------------------------------------------------------
    logic [LABEL_WIDTH-1:0] left_label, top_label;
    logic [LABEL_WIDTH-1:0] label_line [0:MAX_WIDTH-1]; // Stores labels of the previous row

    // Determine left/top labels
    assign left_label = (x == 0) ? 0 : label_line[x - 1];
    assign top_label  = label_line[x];

    // Labeler outputs
    logic                   new_label_valid;
    logic [LABEL_WIDTH-1:0] new_label_value;
    logic                   merge_labels;
    logic [LABEL_WIDTH-1:0] merge_a, merge_b;
    logic [LABEL_WIDTH-1:0] current_label;  // Initial label
    logic [LABEL_WIDTH-1:0] resolved_label; // Final label after merger

    labeler #(
        .LABEL_WIDTH(LABEL_WIDTH)
    ) labeler_inst (
        .clk             (clk),
        .rst             (rst),
        .enable          (enable),
        .last_in_frame   (last_in_frame),
        .motion_pixel    (motion_pixel),
        .left_label      (left_label),
        .top_label       (top_label),
        .new_label_valid (new_label_valid),
        .new_label_value (new_label_value),
        .merge_labels    (merge_labels),
        .merge_a         (merge_a),
        .merge_b         (merge_b),
        .current_label   (current_label)
    );

    // Line Buffer Update
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            for (int i = 0; i < MAX_WIDTH; i++)
                label_line[i] <= 0;
        end else if (enable) begin
            if (motion_pixel) begin
                label_line[x] <= resolved_label;
            end else begin
                label_line[x] <= '0;
            end

            if (last_in_frame) begin
                for (int i = 0; i < MAX_WIDTH; i++)
                    label_line[i] <= 0;
            end
        end
    end

    // -------------------------------------------------------------------------
    // Stage 2: Merger
    // -------------------------------------------------------------------------
    label_merger #(
        .LABEL_WIDTH(LABEL_WIDTH)
    ) merger_inst (
        .clk           (clk),
        .rst           (rst),
        .enable        (enable),
        .last_in_frame (last_in_frame),
        .merge_valid   (merge_labels),
        .merge_a       (merge_a),
        .merge_b       (merge_b),
        .resolve_valid (motion_pixel),
        .resolve_label (current_label),
        .resolved_label(resolved_label)
    );

    // -------------------------------------------------------------------------
    // Bounding Box Storage Banks (Ping-Pong Buffering)
    // -------------------------------------------------------------------------
    // Four banks pipeline the process: Write -> (wait) -> Filter -> Output -> Clear
    logic [1:0] bank_select;

    typedef struct packed {
        logic [WIDTH_BITS-1:0]  min_x;
        logic [HEIGHT_BITS-1:0] min_y;
        logic [WIDTH_BITS-1:0]  max_x;
        logic [HEIGHT_BITS-1:0] max_y;
        logic                   label_active;
        logic                   is_root;
    } bbox_s;

    bbox_s banks [4][NUM_LABELS];

    // Bank Rotation Logic
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            bank_select <= 2'b00;
        end else if (enable && last_in_frame) begin
            case (bank_select)
                2'b00: bank_select <= 2'b01;
                2'b01: bank_select <= 2'b10;
                2'b10: bank_select <= 2'b11;
                2'b11: bank_select <= 2'b00;
            endcase
        end
    end

    logic [1:0] input_bank_idx;
    logic [1:0] filter_bank_idx;
    logic [1:0] output_bank_idx;
    logic [1:0] clear_bank_idx;

    always_comb begin
        input_bank_idx  = bank_select;
        clear_bank_idx  = (bank_select + 2'b01) % 4;
        output_bank_idx = (bank_select + 2'b10) % 4;
        filter_bank_idx = (bank_select + 2'b11) % 4;
    end

    // -------------------------------------------------------------------------
    // Bounding Box Filtering Logic
    // -------------------------------------------------------------------------
    typedef enum logic {
        IDLE,
        FILTER
    } state_t;

    state_t filter_state;
    logic [LABEL_WIDTH-1:0] merge_i;
    logic [LABEL_WIDTH-1:0] merge_j;
    logic                   not_root;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            filter_state <= IDLE;
            merge_i      <= 1;
            merge_j      <= 2;
        end else begin
            case (filter_state)
                IDLE: begin
                    if (last_in_frame) begin
                        filter_state <= FILTER;
                    end
                    merge_i <= 1;
                    merge_j <= 2;
                end

                FILTER: begin
                    if (merge_i < NUM_LABELS - 1) begin
                        if (merge_j < NUM_LABELS - 1 && !not_root) begin
                            merge_j <= merge_j + 1;
                        end else begin
                            merge_i <= merge_i + 1;
                            merge_j <= 1;
                        end
                    end else begin
                        filter_state <= IDLE;
                    end
                end
            endcase
        end
    end

    // -------------------------------------------------------------------------
    // Bank Operations: Update, Filter, Clear
    // -------------------------------------------------------------------------
    logic [LABEL_WIDTH-1:0] clear_indx;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            for (int bank_idx = 0; bank_idx < 4; bank_idx++) begin
                for (int i = 0; i < NUM_LABELS; i++) begin
                    banks[bank_idx][i].min_x        <= '1;
                    banks[bank_idx][i].min_y        <= '1;
                    banks[bank_idx][i].max_x        <= 0;
                    banks[bank_idx][i].max_y        <= 0;
                    banks[bank_idx][i].label_active <= 0;
                    banks[bank_idx][i].is_root      <= 0;
                end
            end
            clear_indx <= 0;
        end else if (enable) begin
            // --- Clear Logic ---
            if (last_in_frame) begin
                clear_indx <= 1;
            end else if (clear_indx != 0 && clear_indx < NUM_LABELS) begin
                clear_indx <= clear_indx + 1;
            end else begin
                clear_indx <= 0;
            end

            if (clear_indx != 0 && clear_indx < NUM_LABELS) begin
                banks[clear_bank_idx][clear_indx].min_x        <= '1;
                banks[clear_bank_idx][clear_indx].min_y        <= '1;
                banks[clear_bank_idx][clear_indx].max_x        <= 0;
                banks[clear_bank_idx][clear_indx].max_y        <= 0;
                banks[clear_bank_idx][clear_indx].label_active <= 0;
                banks[clear_bank_idx][clear_indx].is_root      <= 0;
            end

            // --- Input Update Logic ---
            if (motion_pixel) begin
                if (!banks[input_bank_idx][resolved_label].label_active) begin
                    banks[input_bank_idx][resolved_label].min_x        <= x;
                    banks[input_bank_idx][resolved_label].max_x        <= x;
                    banks[input_bank_idx][resolved_label].min_y        <= y;
                    banks[input_bank_idx][resolved_label].max_y        <= y;
                    banks[input_bank_idx][resolved_label].label_active <= 1;
                    banks[input_bank_idx][resolved_label].is_root      <= 1;
                end else begin
                    if (x < banks[input_bank_idx][resolved_label].min_x) banks[input_bank_idx][resolved_label].min_x <= x;
                    if (x > banks[input_bank_idx][resolved_label].max_x) banks[input_bank_idx][resolved_label].max_x <= x;
                    if (y < banks[input_bank_idx][resolved_label].min_y) banks[input_bank_idx][resolved_label].min_y <= y;
                    if (y > banks[input_bank_idx][resolved_label].max_y) banks[input_bank_idx][resolved_label].max_y <= y;
                    banks[input_bank_idx][current_label].is_root <= (resolved_label == current_label) ? 1 : 0;
                end
            end

            /*
            if(clear_indx != 0 && banks[filter_bank_idx][clear_indx].label_active) begin
                $display("Time %0t: DEBUG_RECEIVE: OUT Bbox: label=%0d, Coords=(%0d,%0d)-(%0d,%0d), valid=%0d.",
                    $time, clear_indx, banks[filter_bank_idx][clear_indx].min_x, banks[filter_bank_idx][clear_indx].min_y,
                    banks[filter_bank_idx][clear_indx].max_x, banks[filter_bank_idx][clear_indx].max_y, banks[filter_bank_idx][clear_indx].label_active);
            end
            */

            // --- Filter Merge Logic ---
            if (filter_state == FILTER
                && merge_i < NUM_LABELS
                && merge_j < NUM_LABELS
                && merge_i != merge_j
                && banks[filter_bank_idx][merge_i].label_active
                && banks[filter_bank_idx][merge_j].label_active) begin

                /*$display("Time %0t: (i,j) - (%0d,%0d).", $time, merge_i,merge_j );*/

                if (!(banks[filter_bank_idx][merge_i].max_x + PROX < banks[filter_bank_idx][merge_j].min_x
                      || banks[filter_bank_idx][merge_i].min_x > banks[filter_bank_idx][merge_j].max_x + PROX
                      || banks[filter_bank_idx][merge_i].max_y + PROX < banks[filter_bank_idx][merge_j].min_y
                      || banks[filter_bank_idx][merge_i].min_y > banks[filter_bank_idx][merge_j].max_y + PROX)) begin

                    // Merge j into i
                    banks[filter_bank_idx][merge_i].min_x <= (banks[filter_bank_idx][merge_i].min_x < banks[filter_bank_idx][merge_j].min_x)
                                                             ? banks[filter_bank_idx][merge_i].min_x
                                                             : banks[filter_bank_idx][merge_j].min_x;
                    banks[filter_bank_idx][merge_i].min_y <= (banks[filter_bank_idx][merge_i].min_y < banks[filter_bank_idx][merge_j].min_y)
                                                             ? banks[filter_bank_idx][merge_i].min_y
                                                             : banks[filter_bank_idx][merge_j].min_y;
                    banks[filter_bank_idx][merge_i].max_x <= (banks[filter_bank_idx][merge_i].max_x > banks[filter_bank_idx][merge_j].max_x)
                                                             ? banks[filter_bank_idx][merge_i].max_x
                                                             : banks[filter_bank_idx][merge_j].max_x;
                    banks[filter_bank_idx][merge_i].max_y <= (banks[filter_bank_idx][merge_i].max_y > banks[filter_bank_idx][merge_j].max_y)
                                                             ? banks[filter_bank_idx][merge_i].max_y
                                                             : banks[filter_bank_idx][merge_j].max_y;

                    // Deactivate j
                    banks[filter_bank_idx][merge_j].label_active <= 1'b0;

                    /*$display("Time %0t: DEBUG_RECEIVE: MERGED Bbox: label i=%0d, label j=%0d , Coords i=(%0d,%0d)-(%0d,%0d), Coords j=(%0d,%0d)-(%0d,%0d).",
                            $time, merge_i,merge_j, banks[filter_bank_idx][merge_i].min_x, banks[filter_bank_idx][merge_i].min_y,
                            banks[filter_bank_idx][merge_i].max_x, banks[filter_bank_idx][merge_i].max_y,
                            banks[filter_bank_idx][merge_j].min_x, banks[filter_bank_idx][merge_j].min_y,
                            banks[filter_bank_idx][merge_j].max_x, banks[filter_bank_idx][merge_j].max_y);*/
                end
            end
        end
    end

    // -------------------------------------------------------------------------
    // Root Status Logic
    // -------------------------------------------------------------------------
    always_comb begin
        if (!banks[filter_bank_idx][merge_i].is_root) begin
            not_root = 1;
        end else begin
            not_root = 0;
        end
    end

    // -------------------------------------------------------------------------
    // Output Highlighting Logic
    // -------------------------------------------------------------------------
    logic on_any_bbox_edge;

    always_comb begin
        on_any_bbox_edge = 1'b0;

        for (int i = 1; i < NUM_LABELS; i++) begin
            if (banks[output_bank_idx][i].label_active) begin
                // Vertical edge check
                if ((x == banks[output_bank_idx][i].min_x || x == banks[output_bank_idx][i].max_x) &&
                    (banks[output_bank_idx][i].min_y <= y && y <= banks[output_bank_idx][i].max_y)) begin
                    on_any_bbox_edge = 1'b1;
                end
                // Horizontal edge check
                else if ((y == banks[output_bank_idx][i].min_y || y == banks[output_bank_idx][i].max_y) &&
                         (banks[output_bank_idx][i].min_x <= x && x <= banks[output_bank_idx][i].max_x)) begin
                    on_any_bbox_edge = 1'b1;
                end
            end
        end
    end

    typedef enum logic [1:0] {
        IDLE_OUT,
        FILTERING,
        OUTPUTING
    } state_out;

    state_out output_state;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            output_state      <= IDLE_OUT;
            highlighted_pixel <= '0;
            pixel_valid       <= 1'b0;
        end else if (enable) begin
            case (output_state)
                IDLE_OUT: begin
                    if (last_in_frame) begin
                        output_state <= FILTERING;
                    end
                end
                FILTERING: begin
                    if (!enable) begin
                        output_state <= IDLE_OUT;
                    end else if (last_in_frame) begin
                        output_state <= OUTPUTING;
                    end
                end
                OUTPUTING: begin
                    highlighted_pixel <= on_any_bbox_edge ? HIGHLIGHT_COLOR : rgb_pixel;
                    pixel_valid       <= 1'b1;

                    // DEBUG
                    /*
                    if(clear_indx != 0 && banks[output_bank_idx][clear_indx].label_active) begin
                        $display("Time %0t: DEBUG_RECEIVE: OUT Bbox: label=%0d, Coords=(%0d,%0d)-(%0d,%0d), valid=%0d.",
                            $time, clear_indx, banks[output_bank_idx][clear_indx].min_x, banks[output_bank_idx][clear_indx].min_y,
                            banks[output_bank_idx][clear_indx].max_x, banks[output_bank_idx][clear_indx].max_y, banks[output_bank_idx][clear_indx].label_active);
                    end
                    */
                    // END DEBUG
                end
                default: begin
                    output_state      <= IDLE_OUT;
                    highlighted_pixel <= '0;
                    pixel_valid       <= 1'b0;
                end
            endcase
        end else begin
            pixel_valid <= 1'b0;
        end
    end

    /*
    // DEBUG
    logic [WIDTH_BITS-1:0]  x_reg;
    logic [HEIGHT_BITS-1:0] y_reg;
    always_ff @(posedge clk or posedge rst) begin
        x_reg <= x;
        y_reg <= y;
    end
    assign x_out = x_reg;
    assign y_out = y_reg;
    // END DEBUG
    */

endmodule