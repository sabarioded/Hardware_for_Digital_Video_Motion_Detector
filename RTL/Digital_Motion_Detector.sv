/*------------------------------------------------------------------------------
 * File          : Digital_Motion_Detector.sv
 * Project       : Hardware_for_Digital_Video_Motion_Detector
 * Author        : eposmk
 * Creation date : Jul 4, 2025
 * Description   : Top-level module for the Digital Motion Detector system.
 *                 Interfaces with AXI4-Stream (Video) and AXI4-Lite (Control/Mem).
 *------------------------------------------------------------------------------*/

module Digital_Motion_Detector #(
    parameter int WIDTH_BITS       = 11,
    parameter int HEIGHT_BITS      = 10,
    parameter int LABEL_WIDTH      = 8,
    parameter int NUM_LABELS       = 1 << LABEL_WIDTH,
    parameter int MAX_WIDTH        = 1 << WIDTH_BITS,
    parameter logic [31:0] HIGHLIGHT_COLOR = 32'hFF000000,
    parameter STREAM_WIDTH         = 32, // AXI4-Stream data width
    parameter ADDR_WIDTH           = 32, // AXI4-Lite Master address width
    parameter DATA_WIDTH           = 32  // AXI4-Lite Master data width
)(
    input  logic                     clk,
    input  logic                     rst,

    // AXI4-Stream Slave (Input Video)
    input  logic                     s_axis_tvalid,
    output logic                     s_axis_tready,
    input  logic [STREAM_WIDTH-1:0]  s_axis_tdata,
    input  logic                     s_axis_tlast,

    // AXI4-Stream Master (Output Video)
    output logic                     m_axis_tvalid,
    input  logic                     m_axis_tready,
    output logic [STREAM_WIDTH-1:0]  m_axis_tdata,
    output logic                     m_axis_tlast,

    // AXI4-Lite Slave (Configuration)
    // Data layout: {11bit width, 10bit height, 8bit threshold}
    input  logic                     s_axil_valid,
    input  logic [31:0]              s_axil_data,
    output logic                     as_axil_ready,

    // AXI4-Lite Master (Memory Interface)
    // Write Address Channel
    output logic                     m_axi_awvalid,
    input  logic                     m_axi_awready,
    output logic [ADDR_WIDTH-1:0]    m_axi_awaddr,
    // Write Data Channel
    output logic                     m_axi_wvalid,
    input  logic                     m_axi_wready,
    output logic [DATA_WIDTH-1:0]    m_axi_wdata,

    // Read Address Channel
    output logic                     m_axi_arvalid,
    input  logic                     m_axi_arready,
    output logic [ADDR_WIDTH-1:0]    m_axi_araddr,
    // Read Data Channel
    input  logic                     m_axi_rvalid,
    output logic                     m_axi_rready,
    input  logic [DATA_WIDTH-1:0]    m_axi_rdata
);

    // -------------------------------------------------------------------------
    // Configuration Registers
    // -------------------------------------------------------------------------
    logic [10:0]  reg_width;
    logic [9:0]   reg_height;
    logic [7:0]   reg_threshold;
    logic         config_loaded; // Flag: 1 if configuration has been latched

    // -------------------------------------------------------------------------
    // Internal Signals
    // -------------------------------------------------------------------------
    logic                    handshake_ready;
    logic                    mp_enable;
    logic                    wr_background;
    logic [STREAM_WIDTH-1:0] highlighted_pixel;
    logic [STREAM_WIDTH-1:0] memory_pixel;
    logic                    pixel_valid;
    logic                    pixel_last;
    logic                    am_enable;

    // Handshake Check: Ensure all downstream/upstream interfaces are ready
    assign handshake_ready = m_axis_tready && m_axi_awready && m_axi_wready && m_axi_arready && m_axi_rvalid;

    // -------------------------------------------------------------------------
    // Pixel Memory Buffer
    // -------------------------------------------------------------------------
    // Latches the pixel read from memory (via AXI Master)
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            memory_pixel <= '0;
        end else begin
            memory_pixel <= m_axi_rdata;
        end
    end

    // -------------------------------------------------------------------------
    // AXI4-Lite Slave (Configuration)
    // -------------------------------------------------------------------------
    // Latch configuration once when s_axil_valid is asserted.
    assign as_axil_ready = s_axil_valid && !config_loaded;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            reg_width     <= '0;
            reg_height    <= '0;
            reg_threshold <= '0;
            config_loaded <= 1'b0;
        end else begin
            if (s_axil_valid && !config_loaded) begin
                reg_width     <= s_axil_data[10:0];
                reg_height    <= s_axil_data[21:11];
                reg_threshold <= s_axil_data[29:22];
                config_loaded <= 1'b1;
            end
        end
    end

    // -------------------------------------------------------------------------
    // Motion Pipeline Instantiation
    // -------------------------------------------------------------------------
    motion_pipeline #(
        .WIDTH_BITS(WIDTH_BITS),
        .HEIGHT_BITS(HEIGHT_BITS),
        .LABEL_WIDTH(LABEL_WIDTH),
        .NUM_LABELS(NUM_LABELS),
        .MAX_WIDTH(MAX_WIDTH),
        .HIGHLIGHT_COLOR(HIGHLIGHT_COLOR)
    ) mp (
        .clk              (clk),
        .rst              (rst),
        .enable           (mp_enable),
        .rbg_pixel        (s_axis_tdata),
        .memory_pixel     (memory_pixel),
        .last_in_frame    (s_axis_tlast),
        .wr_background    (wr_background),
        .threshold        (reg_threshold),
        .width            (reg_width),
        .height           (reg_height),
        .highlighted_pixel(highlighted_pixel),
        .pixel_valid      (pixel_valid),
        .pixel_last       (pixel_last)
    );

    // Output assignments
    assign m_axis_tdata = highlighted_pixel;
    assign m_axis_tlast = pixel_last;

    // -------------------------------------------------------------------------
    // Main Control FSM
    // -------------------------------------------------------------------------
    typedef enum logic [1:0] {
        IDLE,
        PROCESS_FIRST_FRAME,
        PROCESS_FRAME
    } fsm_state_t;

    fsm_state_t current_state, next_state;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            current_state <= IDLE;
        end else begin
            current_state <= next_state;
        end
    end

    always_comb begin
        next_state = current_state;

        // Default Control Signals
        mp_enable     = 0;
        s_axis_tready = 0;
        wr_background = 0;
        m_axis_tvalid = 0;
        am_enable     = 0;

        // Default AXI Master Signals
        m_axi_awvalid = 0;
        m_axi_arvalid = 0;
        m_axi_wvalid  = 0;
        m_axi_wdata   = s_axis_tdata; // Write through input pixel
        m_axi_rready  = 0;

        case (current_state)
            IDLE: begin
                if (config_loaded && handshake_ready) begin
                    next_state    = PROCESS_FIRST_FRAME;
                    s_axis_tready = 1;

                    if (s_axis_tvalid) begin
                        mp_enable      = 1;
                        am_enable      = 1;
                        m_axi_awvalid  = 1;
                        m_axi_arvalid  = 1;
                        m_axi_wvalid   = 1;
                        m_axi_rready   = 1;
                    end
                end else begin
                    next_state = IDLE;
                end
            end

            PROCESS_FIRST_FRAME: begin
                wr_background = 1; // Force background update for the first frame

                if (handshake_ready && s_axis_tvalid) begin
                    mp_enable     = 1;
                    s_axis_tready = 1;
                    am_enable     = 1;
                    m_axi_awvalid = 1;
                    m_axi_arvalid = 1;
                    m_axi_wvalid  = 1;
                    m_axi_rready  = 1;
                end else if (handshake_ready && !s_axis_tvalid) begin
                    s_axis_tready = 1;
                end

                if (s_axis_tlast && s_axis_tvalid) begin
                    next_state = PROCESS_FRAME;
                end
            end

            PROCESS_FRAME: begin
                if (handshake_ready && s_axis_tvalid) begin
                    mp_enable     = 1;
                    s_axis_tready = 1;
                    m_axis_tvalid = pixel_valid;
                    am_enable     = 1;
                    m_axi_awvalid = 1;
                    m_axi_arvalid = 1;
                    m_axi_wvalid  = 1;
                    m_axi_rready  = 1;
                end else if (handshake_ready && !s_axis_tvalid) begin
                    s_axis_tready = 1;
                end
            end

            default: begin
                next_state = IDLE;
            end
        endcase
    end

    // -------------------------------------------------------------------------
    // Address Manager Instantiation
    // -------------------------------------------------------------------------
    addr_manager am (
        .clk       (clk),
        .rst       (rst),
        .enable    (am_enable),
        .last      (s_axis_tlast),
        .write_addr(m_axi_awaddr),
        .read_addr (m_axi_araddr)
    );

`ifndef SYNTHESIS
`ifdef ENABLE_DMD_ASSERTIONS

    // -------------------------------------------------------------------------
    // Assertions
    // -------------------------------------------------------------------------

    // AXI4-Lite Slave Logic
    axil_ready_assert: assert property (
        @(posedge clk) disable iff (rst)
        (s_axil_valid && !config_loaded) |-> as_axil_ready
    ) else $fatal("AXI4-Lite Slave not ready when it should be.");

    axil_config_update_assert: assert property (
        @(posedge clk) disable iff (rst)
        (s_axil_valid && !config_loaded) |=>
        (reg_width     == $past(s_axil_data[10:0]) &&
         reg_height    == $past(s_axil_data[21:11]) &&
         reg_threshold == $past(s_axil_data[29:22]))
    ) else $fatal("AXI4-Lite Configuration registers did not update correctly.");

    config_loaded_set_assert: assert property (
        @(posedge clk) disable iff (rst)
        (s_axil_valid && !config_loaded) |=> config_loaded
    ) else $fatal("config_loaded flag did not set after valid configuration.");

    config_registers_stable_assert: assert property (
        @(posedge clk) disable iff (rst)
        (config_loaded) |=>
        ($stable(reg_width) && $stable(reg_height) && $stable(reg_threshold))
    ) else $fatal("AXI4-Lite Configuration registers changed after config_loaded.");

    // FSM Transitions
    fsm_idle_to_first_frame_assert: assert property (
        @(posedge clk) disable iff (rst)
        (current_state == IDLE && config_loaded && handshake_ready) |=>
        (current_state == PROCESS_FIRST_FRAME)
    ) else $fatal("FSM failed to transition from IDLE to PROCESS_FIRST_FRAME.");

    fsm_first_frame_to_process_assert: assert property (
        @(posedge clk) disable iff (rst)
        (current_state == PROCESS_FIRST_FRAME && s_axis_tlast && s_axis_tvalid) |=>
        (current_state == PROCESS_FRAME)
    ) else $fatal("FSM failed to transition PROCESS_FIRST_FRAME->PROCESS_FRAME.");

    // AXI Stream Handshakes
    s_axis_tready_active_assert: assert property (
        @(posedge clk) disable iff (rst)
        ((current_state inside {PROCESS_FIRST_FRAME, PROCESS_FRAME}) && handshake_ready) |-> s_axis_tready
    ) else $fatal("s_axis_tready not active in processing state.");

    s_axis_tready_idle_assert: assert property (
        @(posedge clk) disable iff (rst)
        (current_state == IDLE && !config_loaded) |-> !s_axis_tready
    ) else $fatal("s_axis_tready active in IDLE before config_loaded.");

    // Data Integrity
    always @(posedge clk) begin
        if (m_axis_tvalid && m_axis_tready) begin
            if (m_axis_tdata !== highlighted_pixel) begin
                #1ns;
                if (m_axis_tdata !== highlighted_pixel)
                    $fatal("m_axis_tdata != highlighted_pixel after settle");
            end
        end
    end

    m_axis_tlast_follows_pixel_last_assert: assert property (
        @(posedge clk) disable iff (rst)
        m_axis_tvalid |=> (m_axis_tlast == pixel_last)
    ) else $fatal("m_axis_tlast != pixel_last while valid.");

    // AXI Master
    axi_awvalid_active_assert: assert property (
        @(posedge clk) disable iff (rst)
        (current_state inside {PROCESS_FIRST_FRAME, PROCESS_FRAME} && handshake_ready && s_axis_tvalid) |-> m_axi_awvalid
    ) else $fatal("m_axi_awvalid not asserted in processing.");

    axi_wvalid_active_assert: assert property (
        @(posedge clk) disable iff (rst)
        (current_state inside {PROCESS_FIRST_FRAME, PROCESS_FRAME} && handshake_ready && s_axis_tvalid) |-> m_axi_wvalid
    ) else $fatal("m_axi_wvalid not asserted in processing.");

    axi_arvalid_active_assert: assert property (
        @(posedge clk) disable iff (rst)
        (current_state inside {PROCESS_FIRST_FRAME, PROCESS_FRAME} && handshake_ready && s_axis_tvalid) |-> m_axi_arvalid
    ) else $fatal("m_axi_arvalid not asserted in processing.");

    axi_rready_active_assert: assert property (
        @(posedge clk) disable iff (rst)
        (current_state inside {PROCESS_FIRST_FRAME, PROCESS_FRAME} && handshake_ready && s_axis_tvalid) |-> m_axi_rready
    ) else $fatal("m_axi_rready not asserted in processing.");

    axi_wdata_assignment_assert: assert property (
        @(posedge clk) disable iff (rst)
        (m_axi_wvalid && m_axi_wready) |-> (m_axi_wdata == s_axis_tdata)
    ) else $fatal("m_axi_wdata != s_axis_tdata during valid write.");

    // Internal Signals
    mp_enable_active_assert: assert property (
        @(posedge clk) disable iff (rst)
        (current_state inside {PROCESS_FIRST_FRAME, PROCESS_FRAME} && handshake_ready && s_axis_tvalid) |-> mp_enable
    ) else $fatal("mp_enable inactive when expected.");

    wr_background_assert: assert property (
        @(posedge clk) disable iff (rst)
        wr_background == (current_state == PROCESS_FIRST_FRAME)
    ) else $fatal("wr_background incorrect for state.");

    reset_values_assert: assert property (
        @(posedge clk)
        rst |-> (current_state == IDLE &&
                 reg_width     == '0 &&
                 reg_height    == '0 &&
                 reg_threshold == '0 &&
                 config_loaded == 1'b0 &&
                 memory_pixel  == '0)
    ) else $fatal("Module did not reset correctly.");

`endif
`endif

endmodule
