// Copyright 2025 The Verible Authors.
// Edge case: Initial block (simulation only, no clock)

module clk_edge_initial_block (
  output logic [7:0] init_value
);

  // Initial blocks are simulation-only, no clock required
  initial begin
    init_value = 8'hAA;
    #10;
    init_value = 8'h55;
  end

endmodule

