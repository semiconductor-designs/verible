// Copyright 2025 The Verible Authors.
// Edge case: always_comb with blocking assignments (OK)

module tim_edge_always_comb_blocking (
  input wire [7:0] a,
  input wire [7:0] b,
  output logic [7:0] sum,
  output logic [7:0] product
);

  // always_comb with blocking assignments is correct
  always_comb begin
    sum = a + b;          // Blocking assignment in comb logic is OK
    product = a * b;      // Order matters within the block
  end

endmodule

