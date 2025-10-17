// Error: Using non-existent modport
interface test_intf;
  logic data;
  
  modport existing (input data);
endinterface

module user(test_intf.nonexistent intf);
  // ERROR: modport 'nonexistent' doesn't exist
  logic local;
  
  always_comb begin
    local = intf.data;
  end
endmodule

module top;
  test_intf bus();
  user u(.intf(bus));
endmodule

