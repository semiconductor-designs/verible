// Copyright 2025 The Verible Authors.
// Edge case: Level-sensitive latch (no clock needed)

module clk_edge_latch_no_clock (
  input wire enable,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Latch: level-sensitive, no clock required
  always_latch begin
    if (enable)
      data_out <= data_in;
  end

endmodule

