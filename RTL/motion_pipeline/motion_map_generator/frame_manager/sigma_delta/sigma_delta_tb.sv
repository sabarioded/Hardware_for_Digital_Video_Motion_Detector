/*------------------------------------------------------------------------------
 * File          : sigma_delta_tb.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 5, 2025
 * Description   : UVM testbench for sigma_delta
 *------------------------------------------------------------------------------*/
module sigma_delta_tb;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  sigma_delta_if vif();

  // Instantiate DUT
  sigma_delta dut (
    .clk            (vif.clk),
    .rst            (vif.rst),
    .enable         (vif.enable),
    .wr_background  (vif.wr_background),
    .curr_pixel     (vif.curr_pixel),
    .background     (vif.background),
    .variance       (vif.variance),
    .background_next(vif.background_next),
    .variance_next  (vif.variance_next)
  );

  //--------------------------------------------------------------------------------
  // Functional coverage: covergroup declared at clock edge
  //--------------------------------------------------------------------------------
  covergroup cg_sigma_delta @(posedge vif.clk);
    option.per_instance = 1;

    // Control signals
    rst_cp:          coverpoint vif.rst           { bins active = {1}; bins inactive = {0}; }
    enable_cp:       coverpoint vif.enable        { bins on = {1};    bins off = {0}; }
    wr_bg_cp:        coverpoint vif.wr_background { bins write = {1}; bins no_write = {0}; }

    // Data inputs
    curr_pixel_cp: coverpoint vif.curr_pixel {
      bins min       = {8'd0};
      bins max       = {8'd255};
      bins low       = {[8'd1:8'd63]};
      bins mid       = {[8'd64:8'd191]};
      bins high      = {[8'd192:8'd254]};
    }

    background_cp: coverpoint vif.background {
      bins min       = {8'd0};
      bins max       = {8'd255};
      bins quarter   = {[8'd1:8'd63]};
      bins middle    = {[8'd64:8'd191]};
      bins top_quart = {[8'd192:8'd254]};
    }

    variance_cp: coverpoint vif.variance {
      bins min       = {8'd2};            // initial value
      bins low     = {[8'd3:8'd4]};     // near lower limit
      bins mid       = {[8'd5:8'd250]};   // typical range
      bins high     = {[8'd251:8'd253]}; // near upper limit
      bins max       = {8'd255};
    }

    // Internal delta for motion logic
    diff_cp: coverpoint ((vif.curr_pixel > vif.background)
                         ? vif.curr_pixel - vif.background
                         : vif.background - vif.curr_pixel) {
      bins zero      = {0};
      bins low     = {[1:8]};
      bins mid    = {[9:128]};
      bins high     = {[129:255]};
    }

    // Output updates with meaningful ranges
    bg_next_cp: coverpoint vif.background_next {
      bins min       = {8'd0};
      bins max       = {8'd255};
      bins low       = {[8'd1:8'd63]};
      bins mid       = {[8'd64:8'd191]};
      bins high      = {[8'd192:8'd254]};
    }
    variance_next_cp: coverpoint vif.variance_next {
      bins min       = {8'd2};            // reset default
      bins low    = {[8'd3:8'd4]};     // near lower limit
      bins mid       = {[8'd5:8'd250]};   // typical operation
      bins high     = {[8'd251:8'd253]}; // near upper limit
      bins max       = {8'd255};
    }

  endgroup

  // Instantiate and sample the covergroup
  cg_sigma_delta coverage_inst;
  initial begin
    coverage_inst = new();
  end

  // UVM run
  initial begin
    uvm_config_db#(virtual sigma_delta_if)::set(null, "*", "vif", vif);
    run_test("sigma_delta_test");
  end

  // 35 MHz clock generation -> ~14.285 ns period
  initial begin
    vif.clk = 0;
    forever #14.285 vif.clk = ~vif.clk;
  end

endmodule : sigma_delta_tb
