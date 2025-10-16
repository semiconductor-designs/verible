// Copyright 2025 The Verible Authors.
// Edge case: No sequential logic (no clock needed)

module clk_edge_combinational_only (
  input wire [7:0] a,
  input wire [7:0] b,
  output logic [7:0] sum,
  output logic carry
);

  // Pure combinational logic - no clock needed
  always_comb begin
    {carry, sum} = a + b;
  end

endmodule

