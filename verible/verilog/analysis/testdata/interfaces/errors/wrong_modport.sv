// Error: Using wrong modport direction
interface dir_intf;
  logic [7:0] data;
  
  modport input_only (input data);
  modport output_only (output data);
endinterface

module writer(dir_intf.input_only intf);
  // ERROR: Trying to write to input-only modport
  always_comb begin
    intf.data = 8'hFF;  // Should fail - can't write to input
  end
endmodule

module reader(dir_intf.output_only intf);
  logic [7:0] local;
  
  // ERROR: Trying to read from output-only modport 
  always_comb begin
    local = intf.data;  // Should fail - output doesn't provide input
  end
endmodule

module top;
  dir_intf bus();
  
  writer wr(.intf(bus));
  reader rd(.intf(bus));
endmodule

