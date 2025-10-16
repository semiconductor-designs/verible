// Test case for STR_008: Case statement without default clause
module str_no_default_case_violation (
  input logic [1:0] sel,
  input logic [3:0] data_in,
  output logic [3:0] data_out
);
  // STR_008: Case statement without default
  always_comb begin
    case (sel)
      2'b00: data_out = data_in;
      2'b01: data_out = data_in + 1;
      2'b10: data_out = data_in + 2;
      // Missing default clause!
    endcase
  end
endmodule

// Good: has default clause
module good_case_with_default (
  input logic [1:0] sel,
  input logic [3:0] data_in,
  output logic [3:0] data_out
);
  always_comb begin
    case (sel)
      2'b00: data_out = data_in;
      2'b01: data_out = data_in + 1;
      2'b10: data_out = data_in + 2;
      default: data_out = 4'b0;
    endcase
  end
endmodule

