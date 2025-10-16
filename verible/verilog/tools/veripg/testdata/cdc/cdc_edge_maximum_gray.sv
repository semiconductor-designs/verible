// Copyright 2025 The Verible Authors.
// Edge case: 32-bit Gray code (large practical case)

module cdc_edge_maximum_gray (
  input wire clk_a,
  input wire clk_b,
  input wire rst_n,
  input wire [31:0] counter_in,
  output logic [31:0] counter_out
);

  // 32-bit Gray code - large practical case
  logic [31:0] gray_code;
  logic [31:0] gray_sync1, gray_sync2;
  
  // Binary to Gray (32-bit)
  assign gray_code = counter_in ^ (counter_in >> 1);
  
  // Synchronize
  always_ff @(posedge clk_b or negedge rst_n) begin
    if (!rst_n) begin
      gray_sync1 <= 32'h0;
      gray_sync2 <= 32'h0;
    end else begin
      gray_sync1 <= gray_code;
      gray_sync2 <= gray_sync1;
    end
  end
  
  // Gray to binary (32-bit) - iterative XOR
  integer i;
  always_comb begin
    counter_out[31] = gray_sync2[31];
    for (i = 30; i >= 0; i = i - 1) begin
      counter_out[i] = counter_out[i+1] ^ gray_sync2[i];
    end
  end

endmodule

