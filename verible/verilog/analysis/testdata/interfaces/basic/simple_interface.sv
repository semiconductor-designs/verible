// Simple interface with basic signals
interface simple_intf;
  logic clk;
  logic reset;
  logic [7:0] data;
  logic valid;
endinterface

module producer(simple_intf intf);
  always_ff @(posedge intf.clk) begin
    if (intf.reset) begin
      intf.data <= 8'h0;
      intf.valid <= 1'b0;
    end else begin
      intf.data <= intf.data + 1;
      intf.valid <= 1'b1;
    end
  end
endmodule

module consumer(simple_intf intf);
  logic [7:0] received_data;
  
  always_ff @(posedge intf.clk) begin
    if (intf.valid) begin
      received_data <= intf.data;
    end
  end
endmodule

module top;
  simple_intf bus();
  
  producer prod(.intf(bus));
  consumer cons(.intf(bus));
endmodule

