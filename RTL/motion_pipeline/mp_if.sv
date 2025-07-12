/*------------------------------------------------------------------------------
 * File          : mp_if.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jun 11, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

interface mp_if;

  localparam WIDTH_BITS  = 11;
  localparam HEIGHT_BITS = 10;

  logic clk;
  logic rst;

  logic                   enable;
  logic [31:0]            rbg_pixel;
  logic [31:0]            memory_pixel;
  logic                   wr_background;
  logic                   last_in_frame;
  logic [7:0]             threshold;
  logic [WIDTH_BITS-1:0]  width;
  logic [HEIGHT_BITS-1:0] height;
  logic [31:0]            highlighted_pixel;
  logic                   pixel_valid;
  logic 				  pixel_last;

endinterface
