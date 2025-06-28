/*------------------------------------------------------------------------------
 * File          : bbox_if.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 27, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

interface bbox_if;

localparam WIDTH_BITS  = 11;
localparam HEIGHT_BITS = 10;
localparam LABEL_WIDTH = 8;

logic clk;
logic rst;
logic                         enable;

// Streaming input
logic                         motion_pixel;
logic                         last_in_frame;
// Configuration data. should be constant.
logic [WIDTH_BITS-1:0]       width;
logic [HEIGHT_BITS-1:0]      height;

//outputs
logic                        bbox_valid;
logic [LABEL_WIDTH-1:0]      bbox_label;
logic [LABEL_WIDTH-1:0]      bbox_parent;
logic [WIDTH_BITS-1:0]       bbox_min_x;
logic [HEIGHT_BITS-1:0]      bbox_min_y;
logic [WIDTH_BITS-1:0]       bbox_max_x;
logic [HEIGHT_BITS-1:0]      bbox_max_y;

endinterface