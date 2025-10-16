// Copyright 2025 The Verible Authors.
// Edge case: Clocking blocks for synchronous testbenches

module str_edge_clocking_block (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) data_out <= 8'h00;
    else data_out <= data_in;
  end

endmodule

// Testbench with clocking block
module testbench_clocking;
  logic clk, rst_n;
  logic [7:0] data_in, data_out;
  
  str_edge_clocking_block dut (
    .clk(clk),
    .rst_n(rst_n),
    .data_in(data_in),
    .data_out(data_out)
  );
  
  // Clocking block: Specifies sampling/driving timing
  clocking cb @(posedge clk);
    default input #1step output #2ns;
    output data_in;
    input data_out;
  endclocking
  
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
  
  initial begin
    rst_n = 0;
    #20 rst_n = 1;
    
    // Drive using clocking block
    cb.data_in <= 8'hAA;
    @(cb);
    cb.data_in <= 8'h55;
    @(cb);
    
    #100 $finish;
  end
endmodule

