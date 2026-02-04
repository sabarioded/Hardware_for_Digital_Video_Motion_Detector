/*------------------------------------------------------------------------------
 * File          : fm_if.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 15, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

interface fm_if;
	logic clk;
	logic rst;
	logic enable;
	
	logic [31:0] pixel;
	logic last_in_frame;
	
	logic [7:0] curr_pixel;
	logic [7:0] prev_pixel;
	
	logic wr_background;
	logic [7:0] background_next;
	logic [7:0] variance_next;
	
endinterface: fm_if