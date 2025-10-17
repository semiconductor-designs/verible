// Generic interface with virtual methods (if supported)
interface generic_intf #(parameter type T = logic [7:0]);
  T data;
  logic valid;
  
  modport producer (output data, output valid);
  modport consumer (input data, input valid);
endinterface

module producer_unit #(parameter type DT = logic [15:0])(
  generic_intf#(.T(DT)).producer prod
);
  always_comb begin
    prod.data = '1;
    prod.valid = 1'b1;
  end
endmodule

module consumer_unit #(parameter type DT = logic [15:0])(
  generic_intf#(.T(DT)).consumer cons
);
  DT local_data;
  
  always_comb begin
    if (cons.valid) begin
      local_data = cons.data;
    end
  end
endmodule

module top;
  generic_intf#(.T(logic [31:0])) bus();
  
  producer_unit#(.DT(logic [31:0])) prod(.prod(bus));
  consumer_unit#(.DT(logic [31:0])) cons(.cons(bus));
endmodule

