// Copyright 2025 The Verible Authors.
// Edge case: Replication operator {N{x}}

module wid_edge_replication (
  input wire [7:0] pattern,
  output logic [31:0] replicated
);

  // Replication: {4{8'b}} = 32 bits
  always_comb begin
    replicated = {4{pattern}};  // 4 * 8 = 32 bits
  end

endmodule

