// Copyright 2025 The Verible Authors.
// Edge case: Part-select width calculations

module wid_edge_part_select (
  input wire [31:0] wide_data,
  output logic [7:0] byte0,
  output logic [7:0] byte1,
  output logic [15:0] word0
);

  // Part-select widths are deterministic
  always_comb begin
    byte0 = wide_data[7:0];     // [7:0] = 8 bits
    byte1 = wide_data[15:8];    // [15:8] = 8 bits
    word0 = wide_data[15:0];    // [15:0] = 16 bits
  end

endmodule

