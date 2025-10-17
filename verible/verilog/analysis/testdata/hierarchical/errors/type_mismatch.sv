// Type mismatch error test
// Purpose: Test detection of incompatible types across modules

typedef struct packed {
  logic [7:0] data;
  logic       valid;
} packet_a_t;

typedef struct packed {
  logic [7:0] data;
  logic       ready;  // Different field name than packet_a_t
} packet_b_t;

module producer (
  input  logic     clk,
  output packet_a_t pkt_out
);
  always_ff @(posedge clk) begin
    pkt_out.data  <= 8'hAA;
    pkt_out.valid <= 1'b1;
  end
endmodule

module consumer (
  input  logic     clk,
  input  packet_b_t pkt_in,  // ERROR: Incompatible type
  output logic [7:0] data_out
);
  always_ff @(posedge clk) begin
    data_out <= pkt_in.data;
  end
endmodule

module type_mismatch_system (
  input  logic      clk,
  output logic [7:0] result
);
  packet_a_t internal_pkt;
  
  producer prod (
    .clk(clk),
    .pkt_out(internal_pkt)
  );
  
  // ERROR: Type mismatch - packet_a_t cannot be assigned to packet_b_t
  consumer cons (
    .clk(clk),
    .pkt_in(internal_pkt),  // Type error here
    .data_out(result)
  );
endmodule

