/*------------------------------------------------------------------------------
 * File          : sigma_delta_if.sv
 * Project       : RTL
 * Description   : Interface for sigma_delta_update module WITHOUT clocking block
 *------------------------------------------------------------------------------*/

interface sigma_delta_if;

  // === Clock and Reset ===
  logic clk;
  logic rst;

  // === Inputs ===
  logic enable;
  logic wr_background;
  logic [7:0] curr_pixel;
  logic [7:0] background;
  logic [7:0] variance;

  // === Outputs ===
  logic [7:0] background_next;
  logic [7:0] variance_next;

endinterface
