// Test file for STR_004: Missing module header comment

module str_missing_header(
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);
  // Violation: No header comment explaining module purpose, parameters, or interfaces
  // Should have:
  // //============================================================================
  // // Module: str_missing_header
  // // Description: <purpose>
  // // Parameters: <list>
  // // Interfaces: <description>
  // //============================================================================
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_out <= 8'h00;
    end else begin
      data_out <= data_in;
    end
  end
endmodule

