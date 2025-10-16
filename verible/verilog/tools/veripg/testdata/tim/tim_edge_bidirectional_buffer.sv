// Copyright 2025 The Verible Authors.
// Edge case: Bidirectional buffer (special case, not comb loop)

module tim_edge_bidirectional_buffer (
  input wire enable,
  input wire dir,          // 0=input, 1=output
  inout wire [7:0] data_bus,
  input wire [7:0] data_out,
  output logic [7:0] data_in
);

  // Tristate buffer for bidirectional bus
  // This looks like a loop but isn't (due to tristate)
  assign data_bus = (enable && dir) ? data_out : 8'hzz;
  assign data_in = data_bus;

endmodule

