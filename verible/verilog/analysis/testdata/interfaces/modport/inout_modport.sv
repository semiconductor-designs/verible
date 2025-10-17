// Interface with inout signals in modports
interface bidir_intf;
  logic clk;
  wire [7:0] bidir_data;
  logic dir; // direction control
  
  modport controller (
    input  clk,
    inout  bidir_data,
    output dir
  );
  
  modport device (
    input  clk,
    inout  bidir_data,
    input  dir
  );
endinterface

module controller_unit(bidir_intf.controller ctrl);
  logic [7:0] internal_data;
  
  assign ctrl.bidir_data = ctrl.dir ? internal_data : 8'bz;
  
  always_ff @(posedge ctrl.clk) begin
    ctrl.dir <= ~ctrl.dir;
    internal_data <= internal_data + 1;
  end
endmodule

module device_unit(bidir_intf.device dev);
  logic [7:0] received_data;
  
  always_ff @(posedge dev.clk) begin
    if (!dev.dir) begin
      received_data <= dev.bidir_data;
    end
  end
endmodule

module top;
  bidir_intf bus();
  
  controller_unit ctrl(.ctrl(bus));
  device_unit dev(.dev(bus));
endmodule

