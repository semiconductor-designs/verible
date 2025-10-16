// Copyright 2025 The Verible Authors.
// Edge case: Config declaration for hierarchical override

module default_adder (
  input wire [7:0] a,
  input wire [7:0] b,
  output logic [7:0] sum
);
  assign sum = a + b;
endmodule

module fast_adder (
  input wire [7:0] a,
  input wire [7:0] b,
  output logic [7:0] sum
);
  // Fast implementation
  assign sum = a + b;
endmodule

module str_edge_config_declaration (
  input wire clk,
  input wire rst_n,
  input wire [7:0] a,
  input wire [7:0] b,
  output logic [7:0] result
);

  logic [7:0] sum;
  
  default_adder u_adder (
    .a(a),
    .b(b),
    .sum(sum)
  );
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) result <= 8'h00;
    else result <= sum;
  end

endmodule

// Configuration to override default_adder with fast_adder
config cfg_fast;
  design str_edge_config_declaration;
  instance str_edge_config_declaration.u_adder use fast_adder;
endconfig

