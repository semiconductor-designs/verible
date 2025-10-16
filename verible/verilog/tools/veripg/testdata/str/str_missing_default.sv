// Test file for STR_008: Case statement without default clause

module str_missing_default(
  input wire [2:0] opcode,
  input wire [7:0] a,
  input wire [7:0] b,
  output logic [7:0] result
);
  // Violation: Case statement without default
  always_comb begin
    case (opcode)
      3'b000: result = a + b;
      3'b001: result = a - b;
      3'b010: result = a & b;
      3'b011: result = a | b;
      3'b100: result = a ^ b;
      // Missing: default clause
    endcase
  end
  
  // Correct way:
  // always_comb begin
  //   case (opcode)
  //     3'b000: result = a + b;
  //     3'b001: result = a - b;
  //     3'b010: result = a & b;
  //     3'b011: result = a | b;
  //     3'b100: result = a ^ b;
  //     default: result = 8'h00;
  //   endcase
  // end
endmodule

