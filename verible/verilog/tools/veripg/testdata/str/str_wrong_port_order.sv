// Test file for STR_005: Port ordering (clk, rst, inputs, outputs)

module str_wrong_port_order(
  output logic [7:0] data_out,  // Violation: output before inputs
  input wire [7:0] data_in,
  input wire rst_n,               // Violation: reset after data
  input wire clk                  // Violation: clock should be first
);
  // Correct order should be: clk, rst_n, data_in, data_out
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_out <= 8'h00;
    end else begin
      data_out <= data_in;
    end
  end
endmodule

