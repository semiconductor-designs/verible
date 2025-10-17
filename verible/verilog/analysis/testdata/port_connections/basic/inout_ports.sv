// Inout port connection test

module bidirectional (
  inout wire [7:0] data_bus
);
endmodule

module top;
  wire [7:0] bus;
  
  bidirectional u_bidir (
    .data_bus(bus)
  );
endmodule

