module motion_detector (
    input  logic        clk,
    input  logic        rst,
    input  logic        enable,
    input  logic        sigma_delta_motion,
    input  logic [7:0]  curr_pixel,
    input  logic [7:0]  prev_pixel,
    input  logic [7:0]  threshold,
    output logic        motion_detected
);

    logic [8:0] diff;
    assign diff = (curr_pixel > prev_pixel) ?
                  (curr_pixel - prev_pixel) :
                  (prev_pixel - curr_pixel);

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            motion_detected <= 1'b0;
        end else if (enable) begin
            motion_detected <= (diff > threshold) && sigma_delta_motion;
        end
    end
endmodule
