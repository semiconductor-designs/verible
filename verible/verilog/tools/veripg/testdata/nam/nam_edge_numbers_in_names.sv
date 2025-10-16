// Copyright 2025 The Verible Authors.
// Edge case: Numbers in signal names (acceptable pattern)

module edge_numbers_in_names (
  input wire clk_100mhz,
  input wire clk_50mhz,
  input wire rst_n,
  input wire [7:0] data_lane0,
  input wire [7:0] data_lane1,
  input wire [7:0] data_lane2,
  input wire [7:0] data_lane3,
  output logic [31:0] combined_data
);

  logic [7:0] buffer0;
  logic [7:0] buffer1;
  logic [7:0] buffer2;
  logic [7:0] buffer3;
  
  logic channel_0_valid;
  logic channel_1_valid;
  
  assign combined_data = {buffer3, buffer2, buffer1, buffer0};

endmodule

