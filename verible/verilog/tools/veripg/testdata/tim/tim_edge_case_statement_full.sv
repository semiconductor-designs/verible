// Copyright 2025 The Verible Authors.
// Edge case: Full case statement (no latch)

module tim_edge_case_statement_full (
  input wire [2:0] opcode,
  input wire [7:0] a,
  input wire [7:0] b,
  output logic [7:0] result
);

  // Full case statement with default - no latch
  always_comb begin
    case (opcode)
      3'b000: result = a + b;
      3'b001: result = a - b;
      3'b010: result = a & b;
      3'b011: result = a | b;
      3'b100: result = a ^ b;
      3'b101: result = ~a;
      3'b110: result = a << 1;
      3'b111: result = a >> 1;
      default: result = 8'h00;  // Explicit default
    endcase
  end

endmodule

