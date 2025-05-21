/*------------------------------------------------------------------------------
 * File          : fm_tb.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 15, 2025
 * Description   : UVM testbench for frame_manager with functional coverage
 *------------------------------------------------------------------------------*/
module fm_tb;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Instantiate interface
  fm_if vif();

  // Instantiate DUT
  frame_manager dut (
    .clk            (vif.clk),
    .rst            (vif.rst),
    .enable         (vif.enable),
    .pixel          (vif.pixel),
    .last_in_frame  (vif.last_in_frame),
    .curr_pixel     (vif.curr_pixel),
    .prev_pixel     (vif.prev_pixel),
    .wr_background  (vif.wr_background),
    .background_next(vif.background_next),
    .variance_next  (vif.variance_next)
  );

  // Clock generation: 100MHz (10ns)
  initial begin
    vif.clk = 0;
    forever #5 vif.clk = ~vif.clk;
  end

  // Reset sequence
  initial begin
    vif.rst = 1;
    #20;
    vif.rst = 0;
  end

  //--------------------------------------------------------------------------------
  // Functional coverage: covergroup declared at clock edge
  //--------------------------------------------------------------------------------
  covergroup cg_fm @(posedge vif.clk);
    option.per_instance = 1;

    // Control signals
    rst_cp:        coverpoint vif.rst           { bins active = {1}; bins inactive = {0}; }
    enable_cp:     coverpoint vif.enable        { bins on     = {1}; bins off      = {0}; }
    last_frame_cp: coverpoint vif.last_in_frame { bins asserted = {1}; bins idle     = {0}; }
    wr_bg_cp:      coverpoint vif.wr_background { bins write     = {1}; bins no_write = {0}; }

        // Data inputs: full 32-bit pixel space in non-overlapping bins
    pixel_cp: coverpoint vif.pixel {
      bins min     = {32'h00000000};                       // zero
      bins low     = {[32'h00000001:32'h3FFFFFFF]};        // low range
      bins mid_lo  = {[32'h40000000:32'h7FFFFFFF]};        // mid lower
      bins mid_hi  = {[32'h80000000:32'hBFFFFFFF]};        // mid upper
      bins high    = {[32'hC0000000:32'hFFFFFFFE]};        // high range
      bins max     = {32'hFFFFFFFF};                       // all ones
    }

    // Frame data: current and previous pixels in non-overlapping bins
    curr_cp: coverpoint vif.curr_pixel {
      bins min     = {8'd0};                              // zero
      bins low     = {[8'd1:8'd63]};                       // low
      bins mid     = {[8'd64:8'd191]};                     // mid
      bins high    = {[8'd192:8'd254]};                    // high
      bins max     = {8'd255};                             // max
    }
    prev_cp: coverpoint vif.prev_pixel {
      bins min     = {8'd0};                              // zero
      bins low     = {[8'd1:8'd63]};                       // low
      bins mid     = {[8'd64:8'd191]};                     // mid
      bins high    = {[8'd192:8'd254]};                    // high
      bins max     = {8'd255};                             // max
    }

    // Output updates: background_next and variance_next in non-overlapping bins
    bg_next_cp: coverpoint vif.background_next {
      bins min     = {8'd0};                              // zero
      bins low     = {[8'd1:8'd63]};                       // low
      bins mid     = {[8'd64:8'd191]};                     // mid
      bins high    = {[8'd192:8'd254]};                    // high
      bins max     = {8'd255};                             // max
    }
    var_next_cp: coverpoint vif.variance_next {
      bins min     = {8'd2};                              // reset default
      bins low     = {[8'd3:8'd9]};                        // low increment boundary
      bins mid     = {[8'd10:8'd246]};                     // mid
      bins high    = {[8'd247:8'd253]};                    // high decrement boundary
      bins max     = {8'd255};                             // max
    }

  endgroup

  // Instantiate and sample coverage
  cg_fm coverage_inst;
  initial begin
    coverage_inst = new();
  end

  // UVM run
  initial begin
    uvm_config_db#(virtual fm_if)::set(null, "*", "vif", vif);
    run_test("fm_test");
  end

endmodule : fm_tb
