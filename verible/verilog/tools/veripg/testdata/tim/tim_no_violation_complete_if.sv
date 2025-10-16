// Copyright 2025 The Verible Authors.
// Negative test: Complete if-else (no latch) - NO violation

module tim_no_violation_complete_if (
  input wire [1:0] sel,
  input wire [7:0] a,
  input wire [7:0] b,
  input wire [7:0] c,
  output logic [7:0] result
);

  // Complete if-else chain - no latch inferred
  always_comb begin
    if (sel == 2'b00)
      result = a;
    else if (sel == 2'b01)
      result = b;
    else if (sel == 2'b10)
      result = c;
    else
      result = 8'h00;  // Default case prevents latch
  end

endmodule

