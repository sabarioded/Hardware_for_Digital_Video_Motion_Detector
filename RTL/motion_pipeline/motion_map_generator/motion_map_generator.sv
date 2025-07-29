/*------------------------------------------------------------------------------
 * File         : motion_map_generator.sv
 * Project      : RTL
 * Author       : eposmk
 * Creation date: May 17, 2025
 * Description  : Top-level motion map generator integrating frame_manager and motion_detector
 *------------------------------------------------------------------------------*/

module motion_map_generator (
  input  logic        clk,
  input  logic        rst,
  input  logic        enable,
  input  logic        last_in_frame,
  input  logic        wr_background,
  input  logic [7:0]  threshold,
  input  logic [31:0] pixel,
  output logic        motion_detected
);

  // Internal pixels and sigma-delta outputs
  logic [7:0] prev_pixel;
  logic [7:0] curr_pixel;
  logic [7:0] background_next;
  logic [7:0] variance_next;

  frame_manager fm_inst (
	.clk           (clk),
	.rst           (rst),
	.enable        (enable),
	.pixel         (pixel),
	.last_in_frame (last_in_frame),
	.curr_pixel    (curr_pixel),
	.prev_pixel    (prev_pixel),
	.wr_background (wr_background),
	.background_next(background_next),
	.variance_next (variance_next)
  );

  motion_detector md_inst (
	.clk             (clk),
	.rst             (rst),
	.enable          (enable),
	.background      (background_next),
	.variance        (variance_next),
	.curr_pixel      (curr_pixel),
	.prev_pixel      (prev_pixel),
	.threshold       (threshold),
	.motion_detected (motion_detected)
  );

// Inline assertions (excluded during synthesis)
`ifndef SYNTHESIS
`ifdef ENABLE_MMG_ASSERTIONS

  // [1] After reset, motion_detected should be low
  always @(posedge clk) begin
    if (rst) begin
      #1;
      assert (!motion_detected)
        else `uvm_fatal("MMG_A1",
             $sformatf("[%0t] MMG_A1: motion_detected=%0d not low after reset",
                       $time, motion_detected));
    end
  end

`endif // ENABLE_MMG_ASSERTIONS
`endif // SYNTHESIS


endmodule: motion_map_generator
