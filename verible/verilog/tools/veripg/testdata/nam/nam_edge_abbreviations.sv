// Copyright 2025 The Verible Authors.
// Edge case: Common abbreviations (clk, rst, addr, data - OK)

module edge_abbreviations (
  input wire clk,      // "clk" abbreviation OK
  input wire rst,      // "rst" abbreviation OK
  input wire [7:0] addr,   // "addr" abbreviation OK
  input wire [31:0] data,  // "data" OK
  output logic ack,        // "ack" abbreviation OK
  output logic rdy         // "rdy" abbreviation OK (3 chars)
);

  logic cfg;  // "cfg" = 3 chars (minimum acceptable)
  logic ena;  // "ena" = 3 chars
  
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      ack <= 1'b0;
      rdy <= 1'b0;
    end
  end

endmodule

