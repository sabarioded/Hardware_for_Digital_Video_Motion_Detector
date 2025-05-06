module frames_buffer (
    input  logic        clk,
    input  logic        rst,
    input  logic [31:0]  rgb_pixel,
    output logic [7:0]  gray_pixel
);
    logic [] Gt

    logic [7:0] gray_pixel_temp;
    // Convert RGB to grayscale using the luminosity method
    // Y = 0.299*R + 0.587*G + 0.114*B
    // Y = (R * 77 + G * 150 + B * 29) / 256
    assign gray_pixel_temp = (rgb_pixel[31:24] * 77 + rgb_pixel[23:16] * 150 + rgb_pixel[15:8] * 29) >> 8;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            gray_pixel <= 8'd0;
        end else begin
            // Convert RGB to grayscale using the luminosity method
        end
    end



// chatGPT
    module frames_buffer #(
    parameter WIDTH = 640,
    parameter HEIGHT = 480
)(
    input  logic        clk,
    input  logic        rst,
    input  logic [31:0] rgb_pixel,       // Incoming RGB pixel (1 at a time)
    input  logic [1:0]  frame_select,    // 0 = gt0, 1 = gt1, 2 = gt2
    input  logic [18:0] pixel_addr,      // Address of the pixel in the frame (up to 640*480 = 307200 = 19 bits)
    input  logic        write_en,        // Enable writing to the selected frame
    input  logic        read_en,         // Enable reading from the selected frame
    output logic [7:0]  gray_pixel_out   // Output grayscale pixel
);

    // 3 frame buffers for grayscale pixels
    logic [7:0] gt0 [0:WIDTH*HEIGHT-1];
    logic [7:0] gt1 [0:WIDTH*HEIGHT-1];
    logic [7:0] gt2 [0:WIDTH*HEIGHT-1];

    // Convert RGB to grayscale
    logic [15:0] r_mult, g_mult, b_mult;
    logic [15:0] gray_sum;
    logic [7:0]  gray_pixel_temp;

    always_comb begin
        r_mult = rgb_pixel[31:24] * 8'd77;
        g_mult = rgb_pixel[23:16] * 8'd150;
        b_mult = rgb_pixel[15:8]  * 8'd29;
        gray_sum = r_mult + g_mult + b_mult;
        gray_pixel_temp = gray_sum[15:8]; // divide by 256
    end

    // Frame write logic
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            // Optional: zero out frame buffers if needed
        end else if (write_en) begin
            case (frame_select)
                2'd0: gt0[pixel_addr] <= gray_pixel_temp;
                2'd1: gt1[pixel_addr] <= gray_pixel_temp;
                2'd2: gt2[pixel_addr] <= gray_pixel_temp;
                default: ; // Do nothing
            endcase
        end
    end

    // Frame read logic
    always_ff @(posedge clk) begin
        if (read_en) begin
            case (frame_select)
                2'd0: gray_pixel_out <= gt0[pixel_addr];
                2'd1: gray_pixel_out <= gt1[pixel_addr];
                2'd2: gray_pixel_out <= gt2[pixel_addr];
                default: gray_pixel_out <= 8'd0;
            endcase
        end
    end

endmodule
