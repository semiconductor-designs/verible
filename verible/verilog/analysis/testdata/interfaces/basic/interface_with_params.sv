// Interface with parameters
interface param_intf #(
  parameter WIDTH = 8,
  parameter DEPTH = 4
);
  logic clk;
  logic [WIDTH-1:0] data;
  logic [$clog2(DEPTH)-1:0] addr;
endinterface

module param_user #(
  parameter W = 16
) (
  param_intf #(.WIDTH(W)) intf
);
  always_ff @(posedge intf.clk) begin
    intf.data <= intf.data + 1;
  end
endmodule

module top;
  param_intf #(.WIDTH(16), .DEPTH(8)) bus();
  param_user #(.W(16)) user(.intf(bus));
endmodule

