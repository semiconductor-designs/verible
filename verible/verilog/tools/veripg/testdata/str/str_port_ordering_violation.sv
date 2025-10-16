// Test case for STR_005: Port ordering (should be: clk, rst, inputs, outputs)
module str_port_ordering_violation (
  output logic data_out,     // STR_005: output before clk/rst
  input logic data_in,
  input logic clk,           // clk should be first
  input logic rst_n          // rst should be second
);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      data_out <= 0;
    else
      data_out <= data_in;
  end
endmodule

// Good: clk, rst, inputs, outputs
module good_port_ordering (
  input logic clk,
  input logic rst_n,
  input logic data_in,
  output logic data_out
);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      data_out <= 0;
    else
      data_out <= data_in;
  end
endmodule

