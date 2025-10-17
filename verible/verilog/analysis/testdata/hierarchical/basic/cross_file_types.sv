// Cross-file type reference test
// Purpose: Test type definitions used across module boundaries

typedef struct packed {
  logic [7:0] data;
  logic       valid;
  logic       ready;
} bus_t;

module producer (
  input  logic  clk,
  output bus_t  bus_out
);
  always_ff @(posedge clk) begin
    bus_out.data  <= 8'hAA;
    bus_out.valid <= 1'b1;
    bus_out.ready <= 1'b1;
  end
endmodule

module consumer (
  input  logic clk,
  input  bus_t bus_in,
  output logic [7:0] data_out
);
  always_ff @(posedge clk) begin
    if (bus_in.valid && bus_in.ready)
      data_out <= bus_in.data;
  end
endmodule

module system (
  input  logic       clk,
  output logic [7:0] final_data
);
  bus_t internal_bus;
  
  producer prod (
    .clk(clk),
    .bus_out(internal_bus)
  );
  
  consumer cons (
    .clk(clk),
    .bus_in(internal_bus),
    .data_out(final_data)
  );
endmodule

