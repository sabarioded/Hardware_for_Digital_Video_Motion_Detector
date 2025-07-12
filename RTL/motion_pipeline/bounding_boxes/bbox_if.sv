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
logic [31:0]					rbg_pixel;
// Configuration data. should be constant.
logic [WIDTH_BITS-1:0]       width;
logic [HEIGHT_BITS-1:0]      height;

//outputs
logic [31:0] highlighted_pixel;
logic pixel_valid;

// DEBUG
logic [WIDTH_BITS-1:0]  x_out;
logic [HEIGHT_BITS-1:0] y_out;
// END DEBUG

endinterface