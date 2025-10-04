// Test file for verifying JSON export includes text fields for expressions
module test_operators;
  logic a, b, rst_n, enable;
  logic [7:0] data_bus;
  logic result, valid;
  
  // Test unary and binary operators in port connections
  child_module u1 (
    .clk_i(clk),
    .rst_ni(~rst_n),        // Unary NOT operator
    .data_i(a + b),         // Binary addition operator
    .enable_i(!enable),     // Logical NOT operator
    .bus_i(data_bus[7:0]),  // Bit slice
    .data_o(result),
    .valid_o(valid)
  );
  
  // Test more complex expressions
  assign result = (a & b) | (c ^ d);
  assign valid = (counter << 2) + offset;
  
endmodule

