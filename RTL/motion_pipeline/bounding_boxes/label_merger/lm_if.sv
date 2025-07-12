/*------------------------------------------------------------------------------
 * File          : lm_if.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : May 26, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

interface lm_if;
localparam LABEL_WIDTH = 8;  // Supports up to 256 labels

  logic                     clk;
  logic                     rst;
  logic 					enable;
  logic 					last_in_frame;

// Merge interface from labeler
  logic                    merge_valid;
  logic [LABEL_WIDTH-1:0]  merge_a;
  logic [LABEL_WIDTH-1:0]  merge_b;

// Label to resolve
  logic                     resolve_valid;
  logic [LABEL_WIDTH-1:0]  resolve_label;
  logic [LABEL_WIDTH-1:0]  resolved_label;

endinterface
