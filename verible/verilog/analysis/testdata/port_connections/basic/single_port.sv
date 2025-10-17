// Single port module

module single_input (
  input logic clk
);
endmodule

module top;
  logic clock;
  
  single_input u_single (
    .clk(clock)
  );
endmodule

