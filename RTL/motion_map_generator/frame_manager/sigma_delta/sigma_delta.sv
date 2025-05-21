/*------------------------------------------------------------------------------
 * File         : sigma_delta_update.sv
 * Project      : RTL
 * Author       : eposmk
 * Creation date: May 5, 2025
 * Description  : Sigma-Delta background/variance updater with explicit enable hold
 *------------------------------------------------------------------------------*/

module sigma_delta (
  input  logic        clk,
  input  logic        rst,
  input  logic        enable,
  input  logic        wr_background,
  input  logic [7:0]  curr_pixel,
  input  logic [7:0]  background,
  input  logic [7:0]  variance,
  output logic [7:0]  background_next,
  output logic [7:0]  variance_next
);

  // Compute pixel difference
  logic [7:0] diff;
  assign diff = (curr_pixel > background)
			  ? curr_pixel - background
			  : background - curr_pixel;

  // Sequential update, with explicit hold when enable is low
  always_ff @(posedge clk or posedge rst) begin
	if (rst) begin
	  background_next <= 8'd0;
	  variance_next   <= 8'd2;
	end
	else if (!enable) begin
	  // Hold previous outputs
	  background_next <= background_next;
	  variance_next   <= variance_next;
	end
	else begin
	  // === BACKGROUND UPDATE ===
	  if (wr_background) begin
		background_next <= curr_pixel;
	  end
	  else if (curr_pixel > background) begin
		background_next <= (background == 8'd255) ? 8'd255 : background + 1;
	  end
	  else if (curr_pixel < background) begin
		background_next <= (background == 8'd0)   ? 8'd0   : background - 1;
	  end
	  else begin
		background_next <= background;
	  end

	  // === VARIANCE UPDATE ===
	  if (diff > variance) begin
		variance_next <= (variance > 8'd253) ? 8'd255 : variance + 2;
	  end
	  else if (diff < variance) begin
		variance_next <= (variance < 8'd4)   ? 8'd2   : variance - 2;
	  end
	  else begin
		variance_next <= variance;
	  end
	end
  end

// Assertions (excluded during synthesis)
`ifndef SYNTHESIS
`ifdef ENABLE_SIGMA_ASSERTIONS

  // [1] After reset, outputs are known
  always @(posedge clk) begin
    if (rst) begin
      #1;
      assert (background_next == 8'd0 && variance_next == 8'd2)
        else `uvm_fatal("A1",
             $sformatf("[%0t] A1 reset failed: bg=%0d var=%0d",
                       $time, background_next, variance_next));
    end
  end

  // [2] Hold behavior
  always @(posedge clk) begin
    if (!rst && !enable) begin
      #1;
      assert (background_next == $past(background_next) &&
              variance_next   == $past(variance_next))
        else `uvm_fatal("A2",
             $sformatf("[%0t] A2 hold failed: bg=%0d var=%0d",
                       $time, background_next, variance_next));
    end
  end

  // [3] Direct write
  always @(posedge clk) begin
    if (!rst && enable && wr_background) begin
      #1;
      assert (background_next == curr_pixel)
        else `uvm_fatal("A3",
             $sformatf("[%0t] A3 write failed: bg=%0d curr=%0d",
                       $time, background_next, curr_pixel));
    end
  end

  // [4] Increment
  always @(posedge clk) begin
    if (!rst && enable && !wr_background && curr_pixel > background) begin
      #1;
      assert (background_next ==
              (background == 8'd255 ? 8'd255 : background + 1))
        else `uvm_fatal("A4",
             $sformatf("[%0t] A4 increment failed: bg=%0d bg_n=%0d",
                       $time, background, background_next));
    end
  end

  // [5] Decrement
  always @(posedge clk) begin
    if (!rst && enable && !wr_background && curr_pixel < background) begin
      #1;
      assert (background_next ==
              (background == 8'd0   ? 8'd0   : background - 1))
        else `uvm_fatal("A5",
             $sformatf("[%0t] A5 decrement failed: bg=%0d bg_n=%0d",
                       $time, background, background_next));
    end
  end

  // [6] No-change background
  always @(posedge clk) begin
    if (!rst && enable && !wr_background && curr_pixel == background) begin
      #1;
      assert (background_next == background)
        else `uvm_fatal("A6",
             $sformatf("[%0t] A6 no-change failed: bg=%0d bg_n=%0d",
                       $time, background, background_next));
    end
  end

  // [7] Variance increment
  always @(posedge clk) begin
    if (!rst && enable && diff > variance) begin
      #1;
      assert (variance_next ==
              (variance > 8'd253 ? 8'd255 : variance + 2))
        else `uvm_fatal("A7",
             $sformatf("[%0t] A7 var-inc failed: var=%0d var_n=%0d",
                       $time, variance, variance_next));
    end
  end

  // [8] Variance decrement
  always @(posedge clk) begin
    if (!rst && enable && diff < variance) begin
      #1;
      assert (variance_next ==
              (variance < 8'd4   ? 8'd2   : variance - 2))
        else `uvm_fatal("A8",
             $sformatf("[%0t] A8 var-dec failed: var=%0d var_n=%0d",
                       $time, variance, variance_next));
    end
  end

  // [9] No-change variance
  always @(posedge clk) begin
    if (!rst && enable && diff == variance) begin
      #1;
      assert (variance_next == variance)
        else `uvm_fatal("A9",
             $sformatf("[%0t] A9 var-nochg failed: var=%0d var_n=%0d",
                       $time, variance, variance_next));
    end
  end

  // [10] Range
  always @(posedge clk) begin
    if (!rst && enable) begin
      #1;
      assert (background_next >= 0   && background_next <= 8'd255 &&
              variance_next   >= 0   && variance_next   <= 8'd255)
        else `uvm_fatal("A10",
             $sformatf("[%0t] A10 range failed: bg_n=%0d var_n=%0d",
                       $time, background_next, variance_next));
    end
  end

`endif // ENABLE_SIGMA_ASSERTIONS
`endif // SYNTHESIS


endmodule: sigma_delta
