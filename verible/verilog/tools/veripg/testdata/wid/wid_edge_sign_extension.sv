// Copyright 2025 The Verible Authors.
// Edge case: Sign extension (valid width conversion)

module wid_edge_sign_extension (
  input wire signed [7:0] narrow_signed,
  output logic signed [15:0] wide_signed
);

  // Sign extension is valid - MSB is replicated
  always_comb begin
    wide_signed = narrow_signed;  // Automatic sign extension
  end

endmodule

