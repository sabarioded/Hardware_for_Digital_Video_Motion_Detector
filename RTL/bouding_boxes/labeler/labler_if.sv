/*------------------------------------------------------------------------------
 * File          : labler_if.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 23, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

interface labler_if;
localparam LABEL_WIDTH = 8;  // Supports up to 256 labels

// Global clock & reset (driven by TB)
logic clk;
logic rst;

// Signals
logic                   enable;
logic                   motion_pixel;
logic [LABEL_WIDTH-1:0] left_label;
logic [LABEL_WIDTH-1:0] top_label;
logic                   new_label_valid;
logic [LABEL_WIDTH-1:0] new_label_value;
logic                   merge_labels;
logic [LABEL_WIDTH-1:0] merge_a;
logic [LABEL_WIDTH-1:0] merge_b;
logic [LABEL_WIDTH-1:0] current_label;


endinterface