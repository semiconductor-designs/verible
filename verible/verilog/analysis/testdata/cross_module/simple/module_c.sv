// Test file: Leaf module
// module_c is instantiated by module_b (for hierarchical tests)

module module_c (
  input logic clk,
  input logic enable,
  input logic [3:0] data_in,
  output logic [3:0] data_out
);
  
  always_ff @(posedge clk) begin
    if (enable) begin
      data_out <= data_in;
    end
  end
  
endmodule

