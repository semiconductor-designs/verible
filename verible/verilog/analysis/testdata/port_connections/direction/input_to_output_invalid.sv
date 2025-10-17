// Invalid: Cannot directly connect input to output

module driver (
  input logic [7:0] data_in
);
endmodule

module receiver (
  output logic [7:0] data_out
);
endmodule

module top;
  logic [7:0] signal;
  
  // Invalid: Both trying to drive the same signal
  // This would create a driver conflict
  driver u_drv (.data_in(signal));
  receiver u_rcv (.data_out(signal));
endmodule

