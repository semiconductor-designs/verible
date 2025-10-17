// Struct type hierarchy test
// Purpose: Test struct compatibility across modules

typedef struct packed {
  logic [3:0] id;
  logic [7:0] data;
  logic       valid;
} simple_packet_t;

typedef struct packed {
  simple_packet_t payload;
  logic [1:0]     priority;
  logic           error;
} enhanced_packet_t;

module packet_generator (
  input  logic            clk,
  output simple_packet_t  pkt_out
);
  always_ff @(posedge clk) begin
    pkt_out.id    <= 4'h5;
    pkt_out.data  <= 8'hAA;
    pkt_out.valid <= 1'b1;
  end
endmodule

module packet_enhancer (
  input  logic            clk,
  input  simple_packet_t  pkt_in,
  output enhanced_packet_t pkt_out
);
  always_ff @(posedge clk) begin
    pkt_out.payload  <= pkt_in;
    pkt_out.priority <= 2'b10;
    pkt_out.error    <= 1'b0;
  end
endmodule

module packet_system (
  input  logic            clk,
  output enhanced_packet_t final_pkt
);
  simple_packet_t basic_pkt;
  
  packet_generator gen (
    .clk(clk),
    .pkt_out(basic_pkt)
  );
  
  packet_enhancer enh (
    .clk(clk),
    .pkt_in(basic_pkt),
    .pkt_out(final_pkt)
  );
endmodule

