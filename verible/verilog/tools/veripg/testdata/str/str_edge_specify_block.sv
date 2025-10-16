// Copyright 2025 The Verible Authors.
// Edge case: Specify block for timing constraints

module str_edge_specify_block (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) data_out <= 8'h00;
    else data_out <= data_in;
  end
  
  // Specify block: Timing constraints
  specify
    // Setup and hold times
    $setup(data_in, posedge clk, 0.5);
    $hold(posedge clk, data_in, 0.3);
    
    // Propagation delays
    (clk => data_out) = (1.2, 1.5);
    (rst_n => data_out) = (0.8, 1.0);
    
    // Pulse width constraints
    $width(posedge clk, 2.0);
    $width(negedge clk, 2.0);
    
    // Period constraint
    $period(posedge clk, 5.0);
  endspecify

endmodule

