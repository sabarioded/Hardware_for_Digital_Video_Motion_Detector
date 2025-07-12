/*------------------------------------------------------------------------------
 * File          : motion_pipeline.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jun 11, 2025
 * Description   : Top-level motion detection + bounding-box pipeline
 *------------------------------------------------------------------------------*/
module motion_pipeline  #(
  parameter int WIDTH_BITS       = 11,
  parameter int HEIGHT_BITS      = 10,
  parameter int LABEL_WIDTH      = 8,
  parameter int NUM_LABELS       = 1 << LABEL_WIDTH,
  parameter int MAX_WIDTH        = 1 << WIDTH_BITS,
  parameter logic [31:0] HIGHLIGHT_COLOR = 32'hFF000000
) (
  input  logic                   clk,
  input  logic                   rst,

  // Global enable
  input  logic                   enable,

  // Streaming input
  input  logic [31:0]            rbg_pixel,       // {R,G,B,0x00}
  input  logic                   wr_background,   // force reload of background
  input  logic                   last_in_frame,   // end-of-frame flag
  input  logic [7:0]             threshold,       // motion threshold
  input  logic [31:0]            memory_pixel,       // {R,G,B,0x00}

  // Frame size
  input  logic [WIDTH_BITS-1:0]  width,
  input  logic [HEIGHT_BITS-1:0] height,

  // Streaming outputs
  output logic [31:0]            highlighted_pixel,
  output logic                   pixel_valid,
  output logic 					 pixel_last
);
	localparam size =  1280 * 720;
  //---------------------------------------------------------------------------  
  // Timing alignment: motion_map_generator is 1 cycle, bbox_top is 2 cycles
  //---------------------------------------------------------------------------  
  logic [2:0] enable_reg;
  logic [2:0] last_reg;

  always_ff @(posedge clk or posedge rst) begin
	if (rst) begin
	  enable_reg  <= 3'b000;  
	  last_reg    <= 2'b00;   
	end else begin
	  enable_reg  <= { enable_reg[1:0], enable };
	  last_reg    <= { last_reg[1:0],   last_in_frame };
	end
  end
  

  //---------------------------------------------------------------------------  
  // Internal wire from motion_map_generator ? bbox_top
  //---------------------------------------------------------------------------  
  logic motion_pixel;

  //---------------------------------------------------------------------------  
  // 1) Sigma-delta motion map generator
  //---------------------------------------------------------------------------  
  motion_map_generator mmg (
	.clk            (clk),
	.rst            (rst),
	.enable         (enable     || enable_reg[1]),  
	.wr_background  (wr_background),
	.pixel          (rbg_pixel),
	.last_in_frame  (last_in_frame),
	.threshold      (threshold),
	.motion_detected(motion_pixel)
  );

  //---------------------------------------------------------------------------  
  // 2) Bounding-box extractor + painter
  //---------------------------------------------------------------------------  
  bbox_top #(
	.WIDTH_BITS      (WIDTH_BITS),
	.HEIGHT_BITS     (HEIGHT_BITS),
	.LABEL_WIDTH     (LABEL_WIDTH),
	.NUM_LABELS      (NUM_LABELS),
	.MAX_WIDTH       (MAX_WIDTH),
	.HIGHLIGHT_COLOR (HIGHLIGHT_COLOR)
  ) bbox (
	.clk              (clk),
	.rst              (rst),
	.enable           (enable_reg[1] || enable_reg[2]),
	.motion_pixel     (motion_pixel),
	.last_in_frame    (last_reg[1]),
	.rgb_pixel        (memory_pixel),
	.width            (width),
	.height           (height),
	.highlighted_pixel(highlighted_pixel),
	.pixel_valid      (pixel_valid)
  );
  
  assign pixel_last = last_reg[2];

endmodule : motion_pipeline
