/*------------------------------------------------------------------------------
 * File          : dmd_if.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jul 6; 2025
 * Description   :
 *------------------------------------------------------------------------------*/

interface dmd_if;
  logic                     clk;
  logic                     rst;

// AXI4-Stream Slave ( video)
  logic                     s_axis_tvalid;
 logic                     s_axis_tready;
  logic [STREAM_WIDTH-1:0]  s_axis_tdata;
  logic                     s_axis_tlast;

// AXI4-Stream Master ( video)
 logic                     m_axis_tvalid;
  logic                     m_axis_tready;
 logic [STREAM_WIDTH-1:0]  m_axis_tdata;
 logic                     m_axis_tlast;

// AXI4-Lite Slave (config: width/height/threshold)
  logic                     s_axil_valid;
  logic [10:0]              s_axil_width;
  logic [9:0]               s_axil_height;
  logic [7:0]               s_axil_threshold;
 logic                     as_axil_ready; // AXI-Lite Slave Ready

// AXI4-Lite Master (memory for pixels)
// Write Address Channel
 logic                     m_axi_awvalid;
  logic                     m_axi_awready;
 logic [ADDR_WIDTH-1:0]    m_axi_awaddr;
 
// Write Data Channel
 logic                     m_axi_wvalid;
  logic                     m_axi_wready;
 logic [DATA_WIDTH-1:0]    m_axi_wdata;
// Write Response Channel
//  logic                     m_axi_bvalid;
// logic                     m_axi_bready;
//  logic [1:0]               m_axi_bresp; // Response status
// Read Address Channel
 logic                     m_axi_arvalid;
  logic                     m_axi_arready;
 logic [ADDR_WIDTH-1:0]    m_axi_araddr;
// Read Data Channel
  logic                     m_axi_rvalid;
 logic                     m_axi_rready;
  logic [DATA_WIDTH-1:0]    m_axi_rdata;
//  logic [1:0]               m_axi_rresp // Response status
endinterface