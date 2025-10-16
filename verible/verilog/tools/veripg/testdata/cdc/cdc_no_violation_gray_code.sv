// Copyright 2025 The Verible Authors.
// Negative test: Multi-bit CDC with Gray code - NO violations expected

module cdc_no_violation_gray_code (
  input wire clk_a,
  input wire clk_b,
  input wire rst_n,
  input wire [3:0] counter_in,
  output logic [3:0] counter_out
);

  // Gray code conversion for multi-bit CDC
  logic [3:0] gray_code;
  logic [3:0] gray_sync1, gray_sync2;
  
  // Binary to Gray conversion
  assign gray_code = counter_in ^ (counter_in >> 1);
  
  // Two-stage synchronizer for Gray-coded signal
  always_ff @(posedge clk_b or negedge rst_n) begin
    if (!rst_n) begin
      gray_sync1 <= 4'b0;
      gray_sync2 <= 4'b0;
    end else begin
      gray_sync1 <= gray_code;
      gray_sync2 <= gray_sync1;
    end
  end
  
  // Gray to binary conversion
  assign counter_out[3] = gray_sync2[3];
  assign counter_out[2] = counter_out[3] ^ gray_sync2[2];
  assign counter_out[1] = counter_out[2] ^ gray_sync2[1];
  assign counter_out[0] = counter_out[1] ^ gray_sync2[0];

endmodule

