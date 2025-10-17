// Typedef resolution hierarchy test
// Purpose: Test typedef resolution across module boundaries

typedef logic [7:0] byte_t;
typedef byte_t data_byte_t;
typedef data_byte_t payload_t;

typedef struct packed {
  payload_t data;
  logic     valid;
} transfer_t;

module data_source (
  input  logic    clk,
  output payload_t data_out
);
  always_ff @(posedge clk) begin
    data_out <= 8'hFF;
  end
endmodule

module data_wrapper (
  input  logic      clk,
  input  payload_t  data_in,
  output transfer_t transfer_out
);
  always_ff @(posedge clk) begin
    transfer_out.data  <= data_in;
    transfer_out.valid <= 1'b1;
  end
endmodule

module data_unwrapper (
  input  logic      clk,
  input  transfer_t transfer_in,
  output data_byte_t byte_out
);
  always_ff @(posedge clk) begin
    if (transfer_in.valid)
      byte_out <= transfer_in.data;
  end
endmodule

module typedef_system (
  input  logic  clk,
  output byte_t result
);
  payload_t  source_data;
  transfer_t wrapped_data;
  
  data_source src (
    .clk(clk),
    .data_out(source_data)
  );
  
  data_wrapper wrap (
    .clk(clk),
    .data_in(source_data),
    .transfer_out(wrapped_data)
  );
  
  data_unwrapper unwrap (
    .clk(clk),
    .transfer_in(wrapped_data),
    .byte_out(result)
  );
endmodule

