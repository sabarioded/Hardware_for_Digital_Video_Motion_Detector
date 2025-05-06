module box_filter (
    input  logic        clk,
    input  logic        rst,
    input  logic [3:0]  neighbors_number, // Up to 8 neighbors, max value = 8
    input  logic [8:0]  motion_map,       // 3x3 window flattened
    output logic        filtered_motion
);

    logic [4:0] number_of_motion_pixels;

    always_comb begin
        number_of_motion_pixels = motion_map[0] + motion_map[1] + motion_map[2] +
                                  motion_map[3] + motion_map[4] + motion_map[5] +
                                  motion_map[6] + motion_map[7] + motion_map[8];
    end

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            filtered_motion <= 0;
        end else begin
            filtered_motion <= (number_of_motion_pixels > neighbors_number);
        end
    end

endmodule
