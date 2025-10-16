// Copyright 2025 The Verible Authors.
// Edge case: 2-bit Gray code (minimum practical case)

module cdc_edge_minimal_gray (
  input wire clk_a,
  input wire clk_b,
  input wire rst_n,
  input wire [1:0] counter_in,
  output logic [1:0] counter_out
);

  // 2-bit Gray code - minimum case
  logic [1:0] gray_code;
  logic [1:0] gray_sync1, gray_sync2;
  
  // Binary to Gray (2-bit)
  assign gray_code = counter_in ^ (counter_in >> 1);
  
  // Synchronize
  always_ff @(posedge clk_b or negedge rst_n) begin
    if (!rst_n) begin
      gray_sync1 <= 2'b00;
      gray_sync2 <= 2'b00;
    end else begin
      gray_sync1 <= gray_code;
      gray_sync2 <= gray_sync1;
    end
  end
  
  // Gray to binary (2-bit)
  assign counter_out[1] = gray_sync2[1];
  assign counter_out[0] = counter_out[1] ^ gray_sync2[0];

endmodule

