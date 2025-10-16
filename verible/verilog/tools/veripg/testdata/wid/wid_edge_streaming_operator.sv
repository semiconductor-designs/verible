// Copyright 2025 The Verible Authors.
// Edge case: Streaming operators (bit/byte ordering)

module wid_edge_streaming_operator (
  input wire [31:0] data_in,
  output logic [31:0] data_swapped
);

  // Streaming operator for byte swapping
  always_comb begin
    data_swapped = {<<8{data_in}};  // Byte reverse
  end

endmodule

