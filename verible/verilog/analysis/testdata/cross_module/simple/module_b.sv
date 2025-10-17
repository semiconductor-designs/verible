// Test file: Simple module that can be instantiated
// module_b is instantiated by module_a

module module_b (
  input logic clk,
  input logic rst_n,
  input logic [7:0] data_in,
  output logic [7:0] data_out
);
  
  // Simple register
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_out <= 8'h00;
    end else begin
      data_out <= data_in;
    end
  end
  
endmodule

