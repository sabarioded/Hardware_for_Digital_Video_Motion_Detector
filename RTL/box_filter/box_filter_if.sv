/*------------------------------------------------------------------------------
 * File          : box_filter_if.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

interface box_filter_if;

// === Clock & Reset ===
logic clk;
logic rst;

// === Inputs ===
logic        enable;
logic [3:0]  neighbors_number;
logic [8:0]  motion_map;

// === Output ===
logic        filtered_motion;

endinterface