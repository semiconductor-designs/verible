// Test file: Leaf module in 3-level hierarchy

module leaf (
  input logic clk,
  input logic rst_n,
  input logic [7:0] data_in,
  output logic [7:0] data_out
);
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_out <= 8'h00;
    end else begin
      data_out <= data_in;
    end
  end
  
endmodule

