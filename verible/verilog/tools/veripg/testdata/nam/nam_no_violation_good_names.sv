// Copyright 2025 The Verible Authors.
// Negative test: All naming conventions followed - NO violation

module good_naming_example (
  input wire clk_main,
  input wire rst_n,
  input wire enable_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  parameter int BUFFER_DEPTH = 16;
  parameter int DATA_WIDTH = 8;
  
  logic [7:0] buffer_stage1;
  logic [7:0] buffer_stage2;
  logic valid_data;
  
  always_ff @(posedge clk_main or negedge rst_n) begin
    if (!rst_n) begin
      buffer_stage1 <= 8'h00;
      buffer_stage2 <= 8'h00;
      valid_data <= 1'b0;
    end else if (!enable_n) begin
      buffer_stage1 <= data_in;
      buffer_stage2 <= buffer_stage1;
      valid_data <= 1'b1;
    end
  end
  
  assign data_out = buffer_stage2;

endmodule

