// Test case for RST_004: Reset signal used as data
module rst_as_data_violation;
  logic clk, rst_n, data, output_data;
  
  // Valid: rst_n used in sensitivity list
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      data <= 1'b0;
    else
      data <= 1'b1;
  end
  
  // RST_004: Reset used as data (RHS of assignment)
  always_ff @(posedge clk) begin
    output_data <= rst_n;  // VIOLATION: reset used as data!
  end
endmodule

