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

	localparam int DRIVER_DATA_WIDTH = 32;
	localparam int DRIVER_ADDR_WIDTH = 32;

	// Internal memory model for m_axi interface
	// This associative array stores data based on address, simulating a RAM.
	bit [DRIVER_DATA_WIDTH-1:0] mem [bit [DRIVER_ADDR_WIDTH-1:0]];

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

		// Initial reset handling: Wait for reset to be released
		@(posedge vif.clk);
		wait(!vif.rst);

		// Fork the memory responder task to run in parallel.
		// This is crucial because the memory model needs to continuously
		// respond to the DUT's m_axi requests, independent of the main
		// sequence item processing loop.
		fork
			memory_responder();
		join_none

		forever begin
			// Get the next transaction item from the sequencer
			seq_item_port.get_next_item(tr);
			`uvm_info(get_full_name(), $sformatf("Driving transaction: %s", tr.sprint()), UVM_HIGH)

			@(posedge vif.clk);

			// AXI4-Stream Slave (s_axis) - Input Video
			vif.s_axis_tvalid <= tr.s_axis_tvalid;
			vif.s_axis_tdata  <= tr.s_axis_tdata;
			vif.s_axis_tlast  <= tr.s_axis_tlast;

			// AXI4-Stream Master (m_axis) - Output Video (Driver provides tready)
			vif.m_axis_tready <= tr.m_axis_tready; // This simulates the downstream consumer's readiness

			// AXI4-Lite Slave (s_axil) - Configuration (Custom Interface)
			// These are direct inputs to the DUT
			vif.s_axil_valid     <= tr.s_axil_valid;
			vif.s_axil_width     <= tr.s_axil_width;
			vif.s_axil_height    <= tr.s_axil_height;
			vif.s_axil_threshold <= tr.s_axil_threshold;

			// AXI4-Lite Master (m_axi) - Memory Interface (Driver provides ready signals and read data)
			vif.m_axi_awready <= tr.m_axi_awready;
			vif.m_axi_wready  <= tr.m_axi_wready;
			vif.m_axi_arready <= tr.m_axi_arready;
			vif.m_axi_rready  <= tr.m_axi_rready;
			
			seq_item_port.item_done();
		end
	endtask

	// Task to continuously respond to the DUT's AXI4-Lite Master (m_axi) requests
	// This acts as the memory model.
	virtual task memory_responder();
		forever begin
			@(posedge vif.clk); // Sample on clock edge

			// Handle AXI Write Address Channel
			// If DUT asserts awvalid and TB is ready, capture address.
			if (vif.m_axi_awvalid && vif.m_axi_awready) begin
				`uvm_info(get_full_name(), $sformatf("MEM_RESP: AW Handshake. Addr=0x%h", vif.m_axi_awaddr), UVM_HIGH)
			end

			// Handle AXI Write Data Channel
			// If DUT asserts wvalid and TB is ready, capture data and store it.
			if (vif.m_axi_wvalid && vif.m_axi_wready) begin
				mem[vif.m_axi_awaddr] = vif.m_axi_wdata; // Store data at the last received write address
				`uvm_info(get_full_name(), $sformatf("MEM_RESP: W Handshake. Data=0x%h written to 0x%h", vif.m_axi_wdata, vif.m_axi_awaddr), UVM_HIGH)
			end

			// Handle AXI Read Address Channel
			// If DUT asserts arvalid and TB is ready, retrieve data and assert rvalid.
			if (vif.m_axi_arvalid && vif.m_axi_arready) begin
				vif.m_axi_rdata <= mem[vif.m_axi_araddr]; // Provide data from memory model
				vif.m_axi_rvalid <= 1; // Assert rvalid
				`uvm_info(get_full_name(), $sformatf("MEM_RESP: AR Handshake. Addr=0x%h, Data=0x%h (provided)", vif.m_axi_araddr, mem[vif.m_axi_araddr]), UVM_HIGH)
			end else begin
				vif.m_axi_rvalid <= 0; // De-assert rvalid if no valid read request
			end
		end
	endtask

endclass : dmd_driver
