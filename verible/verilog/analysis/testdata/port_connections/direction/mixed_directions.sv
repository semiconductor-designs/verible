// Mixed direction ports in one module

module transceiver (
  input  logic       clk,
  input  logic       rst_n,
  input  logic [7:0] tx_data,
  output logic [7:0] rx_data,
  inout  wire        serial_io
);
endmodule

module top;
  logic       clock;
  logic       reset_n;
  logic [7:0] tx;
  logic [7:0] rx;
  wire        io;
  
  transceiver u_xcvr (
    .clk(clock),
    .rst_n(reset_n),
    .tx_data(tx),
    .rx_data(rx),
    .serial_io(io)
  );
endmodule

