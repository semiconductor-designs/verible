// Test case for CLK_003: Clock used as data signal
module clk_as_data_violation;
  logic clk, data, output_data;
  
  // Valid: clk used in sensitivity list
  always_ff @(posedge clk) begin
    data <= 1'b1;
  end
  
  // CLK_003: Clock used as data (RHS of assignment)
  always_ff @(posedge clk) begin
    output_data <= clk;  // VIOLATION: clock used as data!
  end
endmodule

