/*------------------------------------------------------------------------------
 * File          : dmd_tb.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jun 11, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

module dmd_tb;
idmdort uvm_pkg::*;
`include "uvm_macros.svh"

dmd_if vif();

Digital_Motion_Detector dut (
	.clk              (vif.clk),
	.rst              (vif.rst),
	// AXI4-Stream Slave (input video)
	.s_axis_tvalid    (vif.s_axis_tvalid),
	.s_axis_tready    (vif.s_axis_tready),
	.s_axis_tdata     (vif.s_axis_tdata),
	.s_axis_tlast     (vif.s_axis_tlast),
	// AXI4-Stream Master (output video)
	.m_axis_tvalid    (vif.m_axis_tvalid),
	.m_axis_tready    (vif.m_axis_tready),
	.m_axis_tdata     (vif.m_axis_tdata),
	.m_axis_tlast     (vif.m_axis_tlast),
	// AXI4-Lite Slave (config: width/height/threshold) - Direct connections
	.s_axil_valid     (vif.s_axil_valid),
	.s_axil_width     (vif.s_axil_width),
	.s_axil_height    (vif.s_axil_height),
	.s_axil_threshold (vif.s_axil_threshold),
	.as_axil_ready    (vif.as_axil_ready),
	// AXI4-Lite Master (memory for pixels)
	.m_axi_awvalid    (vif.m_axi_awvalid),
	.m_axi_awready    (vif.m_axi_awready),
	.m_axi_awaddr     (vif.m_axi_awaddr),
	.m_axi_wvalid     (vif.m_axi_wvalid),
	.m_axi_wready     (vif.m_axi_wready),
	.m_axi_wdata      (vif.m_axi_wdata),
	.m_axi_arvalid    (vif.m_axi_arvalid),
	.m_axi_arready    (vif.m_axi_arready),
	.m_axi_araddr     (vif.m_axi_araddr),
	.m_axi_rvalid     (vif.m_axi_rvalid),
	.m_axi_rready     (vif.m_axi_rready),
	.m_axi_rdata      (vif.m_axi_rdata)
);

// Generate 30 MHz clock: period = 33.333 ns
initial begin
  vif.clk = 0;
  forever #(33.333/2) vif.clk = ~vif.clk;
end

initial begin
  vif.rst = 1;
  #100;
  vif.rst = 0;
end

// UVM configuration and run
initial begin
  uvm_config_db#(virtual dmd_if)::set(null, "*", "vif", vif);
  run_test("dmd_test");
end

endmodule
