// Copyright 2025 The Verible Authors.
// Edge case: Zero extension (valid width conversion)

module wid_edge_zero_extension (
  input wire [7:0] narrow_unsigned,
  output logic [15:0] wide_unsigned
);

  // Zero extension is valid - pad with zeros
  always_comb begin
    wide_unsigned = {8'h00, narrow_unsigned};  // Explicit zero extension
  end

endmodule

