// Port type matching - logic to logic

module sender (
  output logic [7:0] data
);
endmodule

module receiver (
  input logic [7:0] data
);
endmodule

module top;
  logic [7:0] connection;
  
  sender u_tx (.data(connection));
  receiver u_rx (.data(connection));
endmodule

