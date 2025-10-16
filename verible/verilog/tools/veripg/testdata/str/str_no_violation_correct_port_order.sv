// Copyright 2025 The Verible Authors.
// Negative test: Correct port ordering - NO violation

module str_no_violation_correct_port_order (
  // 1. Clock signals first
  input wire clk,
  input wire clk_slow,
  
  // 2. Reset signals second
  input wire rst_n,
  input wire soft_rst_n,
  
  // 3. Input signals third
  input wire [7:0] data_in,
  input wire valid_in,
  input wire enable,
  
  // 4. Output signals last
  output logic [7:0] data_out,
  output logic valid_out,
  output logic error
);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_out <= 8'h00;
      valid_out <= 1'b0;
      error <= 1'b0;
    end else begin
      data_out <= data_in;
      valid_out <= valid_in;
      error <= 1'b0;
    end
  end

endmodule

