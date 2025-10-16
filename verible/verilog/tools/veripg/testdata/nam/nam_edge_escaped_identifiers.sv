// Copyright 2025 The Verible Authors.
// Edge case: Escaped identifiers (SystemVerilog feature)

module edge_escaped_identifiers (
  input wire clk,
  input wire rst_n,
  input wire \signal-with-dash ,  // Escaped identifier
  input wire \2wire ,              // Starts with number
  output logic \output$special 
);

  // Escaped identifiers allow special characters
  logic \internal@node ;
  logic \$valid ;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      \internal@node  <= 1'b0;
      \$valid  <= 1'b0;
    end
  end

endmodule

