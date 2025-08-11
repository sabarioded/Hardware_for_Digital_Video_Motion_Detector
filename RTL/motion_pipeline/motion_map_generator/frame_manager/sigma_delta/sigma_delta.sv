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
	  if (wr_background) begin
		  variance_next   <= 8'd2;
		end
	  else if (diff > variance) begin
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

  `ifndef SYNTHESIS
  `ifdef ENABLE_SIGMA_ASSERTIONS

	// ----------------------------------------------------
	// RESET behavior
	// ----------------------------------------------------
	always @(posedge clk) begin
	  if (rst) begin
		#1;
		assert (background_next == 8'd0 && variance_next == 8'd2)
		  else `uvm_fatal("SD_A1",
			$sformatf("[%0t] RESET failed: bg=%0d var=%0d",
					  $time, background_next, variance_next));
	  end
	end

	// ----------------------------------------------------
	// HOLD behavior (when enable=0)
	// ----------------------------------------------------
	always @(posedge clk) begin
	  if (!rst && !enable) begin
		#1;
		assert (background_next == $past(background_next) &&
				variance_next   == $past(variance_next))
		  else `uvm_fatal("SD_A2",
			$sformatf("[%0t] HOLD failed: bg_n=%0d (prev=%0d), var_n=%0d (prev=%0d)",
					  $time,
					  background_next, $past(background_next),
					  variance_next,   $past(variance_next)));
	  end
	end

	// ====================================================
	// BACKGROUND UPDATE RULES
	// ====================================================

	// [1] Direct write when wr_background=1
	always @(posedge clk) begin
	  if (!rst && enable && wr_background) begin
		#1;
		assert (background_next == curr_pixel)
		  else `uvm_fatal("SD_BG1",
			$sformatf("[%0t] BG_WRITE failed: bg_next=%0d expected=%0d",
					  $time, background_next, curr_pixel));
	  end
	end

	// [2] Increment background (+1 but saturate at 255)
	always @(posedge clk) begin
	  if (!rst && enable && !wr_background && curr_pixel > background) begin
		#1;
		assert (background_next ==
				((background == 8'd255) ? 8'd255 : background + 1))
		  else `uvm_fatal("SD_BG2",
			$sformatf("[%0t] BG_INC failed: bg=%0d bg_next=%0d",
					  $time, background, background_next));
	  end
	end

	// [3] Decrement background (-1 but clamp at 0)
	always @(posedge clk) begin
	  if (!rst && enable && !wr_background && curr_pixel < background) begin
		#1;
		assert (background_next ==
				((background == 8'd0) ? 8'd0 : background - 1))
		  else `uvm_fatal("SD_BG3",
			$sformatf("[%0t] BG_DEC failed: bg=%0d bg_next=%0d",
					  $time, background, background_next));
	  end
	end

	// [4] No-change when curr_pixel == background
	always @(posedge clk) begin
	  if (!rst && enable && !wr_background && curr_pixel == background) begin
		#1;
		assert (background_next == background)
		  else `uvm_fatal("SD_BG4",
			$sformatf("[%0t] BG_NOCHG failed: bg=%0d bg_next=%0d",
					  $time, background, background_next));
	  end
	end

	// ====================================================
	// VARIANCE UPDATE RULES
	// ====================================================

	// Variance increment (+2 but saturate at 255)
	always @(posedge clk) begin
	  if (!rst && enable && !wr_background && ( (curr_pixel > background ? curr_pixel - background : background - curr_pixel) > variance )) begin
		#1;
		assert (variance_next ==
				((variance > 8'd253) ? 8'd255 : variance + 2))
		  else `uvm_fatal("SD_VAR1",
			$sformatf("[%0t] VAR_INC failed: var=%0d var_next=%0d",
					  $time, variance, variance_next));
	  end
	end

	// Variance decrement (-2 but clamp at 2)
	always @(posedge clk) begin
	  if (!rst && enable && !wr_background && ( (curr_pixel > background ? curr_pixel - background : background - curr_pixel) < variance )) begin
		#1;
		assert (variance_next ==
				((variance < 8'd4) ? 8'd2 : variance - 2))
		  else `uvm_fatal("SD_VAR2",
			$sformatf("[%0t] VAR_DEC failed: var=%0d var_next=%0d",
					  $time, variance, variance_next));
	  end
	end

	// Variance no-change
	always @(posedge clk) begin
	  if (!rst && enable && !wr_background && ( (curr_pixel > background ? curr_pixel - background : background - curr_pixel) == variance )) begin
		#1;
		assert (variance_next == variance)
		  else `uvm_fatal("SD_VAR3",
			$sformatf("[%0t] VAR_NOCHG failed: var=%0d var_next=%0d",
					  $time, variance, variance_next));
	  end
	end

  `endif // ENABLE_SIGMA_ASSERTIONS
  `endif // SYNTHESIS


endmodule: sigma_delta
