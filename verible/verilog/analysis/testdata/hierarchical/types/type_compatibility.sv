// Type compatibility test
// Purpose: Test cross-module type matching

typedef logic [7:0] byte_t;
typedef logic [15:0] word_t;

typedef struct packed {
  byte_t high;
  byte_t low;
} word_struct_t;

module type_producer (
  input  logic  clk,
  output word_t data_out
);
  always_ff @(posedge clk) begin
    data_out <= 16'hABCD;
  end
endmodule

module type_consumer (
  input  logic       clk,
  input  word_t      data_in,
  output byte_t      high_byte,
  output byte_t      low_byte
);
  word_struct_t structured;
  
  always_ff @(posedge clk) begin
    structured = data_in;
    high_byte  = structured.high;
    low_byte   = structured.low;
  end
endmodule

module type_system (
  input  logic  clk,
  output byte_t out_high,
  output byte_t out_low
);
  word_t internal_word;
  
  type_producer prod (
    .clk(clk),
    .data_out(internal_word)
  );
  
  type_consumer cons (
    .clk(clk),
    .data_in(internal_word),
    .high_byte(out_high),
    .low_byte(out_low)
  );
endmodule

