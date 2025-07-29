/*------------------------------------------------------------------------------
 * File          : dmd_driver.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jul 6, 2025
 * Description   : UVM driver for the Digital_Motion_Detector DUT.
 *------------------------------------------------------------------------------*/

class dmd_driver extends uvm_driver #(dmd_trans);
	// factory
	`uvm_component_utils(dmd_driver)

	//interface
	virtual dmd_if vif;
	
	uvm_analysis_port#(dmd_trans) ap;

	//constructor
	function new(string name = "dmd_driver", uvm_component parent=null);
		super.new(name,parent);
		ap = new("ap",this);
	endfunction

	// grab the virtual interface in build phase
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db#(virtual dmd_if)::get(this, "", "vif", vif)) begin
			`uvm_fatal(get_type_name(), "Virtual interface not found for dmd_driver")
		end
	endfunction
	
	// drive the signals in run phase
	virtual task run_phase(uvm_phase phase);
		dmd_trans tr;
		wait(!vif.rst);
		
		repeat(2) @(posedge vif.clk);
		
		forever begin
			#1ns
			seq_item_port.get_next_item(tr);
			
			// AXI4-Stream Slave (s_axis) - Input Video
			vif.s_axis_tvalid <= tr.s_axis_tvalid;
			vif.s_axis_tdata  <= tr.s_axis_tdata;
			vif.s_axis_tlast  <= tr.s_axis_tlast;

			// AXI4-Stream Master (m_axis) - Output Video (Driver provides tready)
			vif.m_axis_tready <= tr.m_axis_tready; // This simulates the downstream consumer's readiness

			// AXI4-Lite Slave (s_axil) - Configuration (Custom Interface)
			// These are direct inputs to the DUT
			vif.s_axil_valid     <= tr.s_axil_valid;
			vif.s_axil_data     <= tr.s_axil_data;

			// AXI4-Lite Master (m_axi) - Memory Interface (Driver provides ready signals and read data)
			vif.m_axi_awready <= tr.m_axi_awready;
			vif.m_axi_wready  <= tr.m_axi_wready;
			vif.m_axi_arready <= tr.m_axi_arready;
			vif.m_axi_rvalid  <= tr.m_axi_rvalid;
			
			ap.write(tr);
			
			seq_item_port.item_done();
			
			@(posedge vif.clk);
		end
	endtask

endclass : dmd_driver
