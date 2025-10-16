// Copyright 2025 The Verible Authors.
// Edge case: Exactly 3 chars (boundary case for minimum length)

module min (  // 3 chars exactly
  input wire clk,  // 3 chars
  input wire rst,  // 3 chars
  input wire [7:0] dat,  // 3 chars
  output logic ack,  // 3 chars
  output logic rdy   // 3 chars
);

  logic ena;  // 3 chars
  logic cfg;  // 3 chars
  logic sel;  // 3 chars
  
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      ack <= 1'b0;
      rdy <= 1'b0;
      ena <= 1'b0;
    end
  end

endmodule

