/*------------------------------------------------------------------------------
 * File          : dmd_trans.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jul 6, 2025
 * Description   :
 *   UVM sequence_item for Digital_Motion_Detector transactions.
 *------------------------------------------------------------------------------*/

class dmd_trans extends uvm_sequence_item;
  // Parameterized widths
  localparam int STREAM_WIDTH = 32;
  localparam int ADDR_WIDTH   = 32;
  localparam int DATA_WIDTH   = 32;

  // AXI4-Stream Slave (input video)
  rand bit                      s_axis_tvalid;
  bit                      s_axis_tready;
  rand bit [STREAM_WIDTH-1:0]   s_axis_tdata;
  rand bit                      s_axis_tlast;

  // AXI4-Stream Master (output video)
  bit                           m_axis_tvalid;
  rand bit                      m_axis_tready; 
  bit [STREAM_WIDTH-1:0]        m_axis_tdata;
  bit                           m_axis_tlast;

  // AXI4-Lite Slave (config: width/height/threshold)
  rand bit                      s_axil_valid;
  rand bit [10:0]               s_axil_width;
  rand bit [9:0]                s_axil_height;
  rand bit [7:0]                s_axil_threshold;
  bit                           as_axil_ready;

  // AXI4-Lite Master (memory for pixels)
  // Write Address Channel
  rand bit                      m_axi_awvalid;
  bit                           m_axi_awready;
  rand bit [ADDR_WIDTH-1:0]     m_axi_awaddr;
  
  // Write Data Channel
  rand bit                      m_axi_wvalid;
  bit                           m_axi_wready;
  rand bit [DATA_WIDTH-1:0]     m_axi_wdata;

  // Read Address Channel
  rand bit                      m_axi_arvalid;
  bit                           m_axi_arready;
  rand bit [ADDR_WIDTH-1:0]     m_axi_araddr;

  // Read Data Channel
  bit                           m_axi_rvalid;
  rand bit                      m_axi_rready;
  bit [DATA_WIDTH-1:0]          m_axi_rdata;
  
  int frame_id;

  `uvm_object_utils(dmd_trans)

  // Constructor
  function new(string name = "dmd_trans");
	super.new(name);
  endfunction
  
  function void set_all_inactive();
	  s_axis_tvalid = 0;
	  s_axis_tdata = '0;
	  s_axis_tlast = 0;
	  m_axis_tready = 1; // Assume downstream is always ready for output for simplicity

	  s_axil_valid = 0;
	  s_axil_width = '0;
	  s_axil_height = '0;
	  s_axil_threshold = '0;

	  m_axi_awready = 1; // Assume memory is always ready for addresses
	  m_axi_wready = 1;  // Assume memory is always ready for write data
	  m_axi_arready = 1; // Assume memory is always ready for read addresses
	  m_axi_rvalid = 1;  // Assume memory always has valid read data (driver will provide actual data)
	  m_axi_rready = 1;  // Assume always ready to consume read data from memory
	  m_axi_rdata = '0;  // Default read data
  endfunction

endclass : dmd_trans
