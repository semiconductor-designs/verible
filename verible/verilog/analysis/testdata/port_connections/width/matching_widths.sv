// Port width matching - exact match

module width_source (
  output logic [15:0] data_16bit,
  output logic [7:0]  data_8bit,
  output logic [3:0]  data_4bit
);
endmodule

module width_sink (
  input logic [15:0] data_16bit,
  input logic [7:0]  data_8bit,
  input logic [3:0]  data_4bit
);
endmodule

module top;
  logic [15:0] conn_16;
  logic [7:0]  conn_8;
  logic [3:0]  conn_4;
  
  width_source u_src (
    .data_16bit(conn_16),
    .data_8bit(conn_8),
    .data_4bit(conn_4)
  );
  
  width_sink u_snk (
    .data_16bit(conn_16),
    .data_8bit(conn_8),
    .data_4bit(conn_4)
  );
endmodule

