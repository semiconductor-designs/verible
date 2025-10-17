// Type mismatch between ports

typedef struct packed {
  logic [7:0] data;
  logic       valid;
} type_a_t;

typedef struct packed {
  logic [7:0] value;
  logic       enable;
} type_b_t;

module source_a (
  output type_a_t out
);
endmodule

module sink_b (
  input type_b_t in
);
endmodule

module top;
  // Type mismatch: type_a_t vs type_b_t
  // Even though they have same bit width, they're different types
  type_a_t connection;
  
  source_a u_src (.out(connection));
  // This should produce a type mismatch warning/error
  // sink_b u_snk (.in(connection));
endmodule

