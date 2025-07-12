/*------------------------------------------------------------------------------
 * File          : mmg_if.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 17, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

interface mmg_if;
logic clk;
logic rst;
logic enable;

logic [31:0] pixel;
logic last_in_frame;
logic [7:0] threshold;
logic wr_background;

logic motion_detected;

endinterface: mmg_if