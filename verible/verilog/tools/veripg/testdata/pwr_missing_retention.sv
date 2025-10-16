// Test file for PWR_004: Retention register without retention annotation

module pwr_missing_retention(
  input wire clk,
  input wire rst_n,
  input wire save_enable,
  input wire restore_enable,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);
  // Violation: State register that needs to survive power-down without retention annotation
  logic [7:0] state_reg;  // Should have retention annotation
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state_reg <= 8'h00;
    end else if (save_enable) begin
      state_reg <= data_in;  // State saved here should be retained during power-down
    end else if (restore_enable) begin
      data_out <= state_reg;  // State restored here
    end
  end
endmodule

