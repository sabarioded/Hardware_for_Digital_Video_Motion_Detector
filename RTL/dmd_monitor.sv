/*------------------------------------------------------------------------------
 * File          : dmd_monitor.sv
 * Project       : Project_RTL
 * Author        : eposmk
 * Creation date : Jul 6, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class dmd_monitor extends uvm_monitor;
	//factory
	`uvm_component_utils(dmd_monitor)
	
	// interface
	virtual dmd_if vif;
	
	// analysis port (for broadcasting sampled transactions to scoreboard)
	uvm_analysis_port#(dmd_trans) ap_out;
	
	//constructor
	function new(string name = "dmd_monitor", uvm_component parent = null);
		super.new(name,parent);
		ap_out = new("ap_out", this);
	endfunction
	
	// build phase - get the interface
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db#(virtual dmd_if)::get(this,"","vif",vif)) begin
		  `uvm_fatal("MONITOR","Virtual interface 'vif' not found for dmd_monitor")
		end
	endfunction
	
	// Sample signals in the run phase and send the transaction to the scoreboard
	virtual task run_phase(uvm_phase phase);
		dmd_trans tr;
		
		// Wait for reset to be released before starting monitoring
		@(posedge vif.clk); // Wait for one clock cycle
		wait(!vif.rst);     // Wait until reset is de-asserted
		`uvm_info(get_full_name(), "Reset released. Starting monitor operation.", UVM_LOW)
		
		// Continuous monitoring loop
		forever begin
			@(posedge vif.clk); // Sample all signals on every positive clock edge

			// Skip sampling if in reset (or if you want to filter specific phases)
			if (vif.rst) begin
				continue;
			end

			// Create a new transaction object for each sample
			tr = dmd_trans::type_id::create("tr", this);
			
			// Populate the transaction with sampled values from the interface
			// AXI4-Stream Slave (input video)
			tr.s_axis_tvalid    = vif.s_axis_tvalid;
			tr.s_axis_tready    = vif.s_axis_tready;
			tr.s_axis_tdata     = vif.s_axis_tdata;
			tr.s_axis_tlast     = vif.s_axis_tlast;

			// AXI4-Stream Master (output video)
			tr.m_axis_tvalid    = vif.m_axis_tvalid;
			tr.m_axis_tready    = vif.m_axis_tready;
			tr.m_axis_tdata     = vif.m_axis_tdata;
			tr.m_axis_tlast     = vif.m_axis_tlast;

			// AXI4-Lite Slave (config: width/height/threshold) - Custom Interface
			tr.s_axil_valid     = vif.s_axil_valid;
			tr.s_axil_width     = vif.s_axil_width;
			tr.s_axil_height    = vif.s_axil_height;
			tr.s_axil_threshold = vif.s_axil_threshold;
			tr.as_axil_ready    = vif.as_axil_ready;

			// AXI4-Lite Master (memory for pixels)
			tr.m_axi_awvalid    = vif.m_axi_awvalid;
			tr.m_axi_awready    = vif.m_axi_awready;
			tr.m_axi_awaddr     = vif.m_axi_awaddr;
			tr.m_axi_wvalid     = vif.m_axi_wvalid;
			tr.m_axi_wready     = vif.m_axi_wready;
			tr.m_axi_wdata      = vif.m_axi_wdata;
			tr.m_axi_arvalid    = vif.m_axi_arvalid;
			tr.m_axi_arready    = vif.m_axi_arready;
			tr.m_axi_araddr     = vif.m_axi_araddr;
			tr.m_axi_rvalid     = vif.m_axi_rvalid;
			tr.m_axi_rready     = vif.m_axi_rready;
			tr.m_axi_rdata      = vif.m_axi_rdata;

			// Broadcast the sampled transaction to the analysis port
			ap_out.write(tr);

			// Optional: Add UVM_INFO messages for debugging and visibility
			// You can customize these to log specific interface handshakes or data.
			/*if (tr.s_axis_tvalid && tr.s_axis_tready) begin
				`uvm_info(get_full_name(), $sformatf("S_AXIS Handshake: tdata=0x%h, tlast=%0d", tr.s_axis_tdata, tr.s_axis_tlast), UVM_LOW)
			end
			if (tr.m_axis_tvalid && tr.m_axis_tready) begin
				`uvm_info(get_full_name(), $sformatf("M_AXIS Handshake: tdata=0x%h, tlast=%0d", tr.m_axis_tdata, tr.m_axis_tlast), UVM_LOW)
			end
			if (tr.s_axil_valid && tr.as_axil_ready) begin
				`uvm_info(get_full_name(), $sformatf("S_AXIL Config Handshake: width=%0d, height=%0d, threshold=%0d", tr.s_axil_width, tr.s_axil_height, tr.s_axil_threshold), UVM_LOW)
			end
			if (tr.m_axi_awvalid && tr.m_axi_awready) begin
				`uvm_info(get_full_name(), $sformatf("M_AXI AW Handshake: awaddr=0x%h", tr.m_axi_awaddr), UVM_LOW)
			end
			if (tr.m_axi_wvalid && tr.m_axi_wready) begin
				`uvm_info(get_full_name(), $sformatf("M_AXI W Handshake: wdata=0x%h", tr.m_axi_wdata), UVM_LOW)
			end
			if (tr.m_axi_arvalid && tr.m_axi_arready) begin
				`uvm_info(get_full_name(), $sformatf("M_AXI AR Handshake: araddr=0x%h", tr.m_axi_araddr), UVM_LOW)
			end
			if (tr.m_axi_rvalid && tr.m_axi_rready) begin
				`uvm_info(get_full_name(), $sformatf("M_AXI R Handshake: rdata=0x%h", tr.m_axi_rdata), UVM_LOW)
			end*/
		end
	endtask
	
endclass
