// Interface inheritance test
// Purpose: Test interface extends interface

interface base_if (input logic clk);
  logic       valid;
  logic [7:0] data;
  
  modport master (
    output valid,
    output data
  );
  
  modport slave (
    input valid,
    input data
  );
endinterface

interface extended_if (input logic clk) extends base_if;
  logic ready;
  logic error;
  
  modport master (
    output valid,
    output data,
    input  ready,
    output error
  );
  
  modport slave (
    input  valid,
    input  data,
    output ready,
    input  error
  );
endinterface

module master_device (
  input logic clk,
  extended_if.master bus
);
  always_ff @(posedge clk) begin
    bus.valid <= 1'b1;
    bus.data  <= 8'hAA;
    bus.error <= 1'b0;
  end
endmodule

module slave_device (
  input logic clk,
  extended_if.slave bus
);
  always_ff @(posedge clk) begin
    bus.ready <= bus.valid;
  end
endmodule

