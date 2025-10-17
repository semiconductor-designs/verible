// Interface with basic modports
interface bus_intf;
  logic clk;
  logic [7:0] data;
  logic valid;
  logic ready;
  
  // Master modport - drives data/valid, receives ready
  modport master (
    input  clk,
    output data,
    output valid,
    input  ready
  );
  
  // Slave modport - receives data/valid, drives ready
  modport slave (
    input  clk,
    input  data,
    input  valid,
    output ready
  );
endinterface

module master_device(bus_intf.master mst);
  always_ff @(posedge mst.clk) begin
    if (mst.ready) begin
      mst.data <= mst.data + 1;
      mst.valid <= 1'b1;
    end
  end
endmodule

module slave_device(bus_intf.slave slv);
  always_ff @(posedge slv.clk) begin
    if (slv.valid) begin
      slv.ready <= 1'b1;
    end
  end
endmodule

module top;
  bus_intf bus();
  
  master_device master(.mst(bus));
  slave_device slave(.slv(bus));
endmodule

