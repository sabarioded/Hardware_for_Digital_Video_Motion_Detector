/*------------------------------------------------------------------------------
 * File          : motion_detector_if.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

interface motion_detector_if;

  // === Clock and Reset ===
  logic clk;
  logic rst;
  
  // Input
  logic        enable;
  logic [7:0]  background;
  logic [7:0]  variance;
  logic [7:0]  curr_pixel;
  logic [7:0]  prev_pixel;
  logic [7:0]  threshold;

  // Output
  logic            motion_detected;

endinterface