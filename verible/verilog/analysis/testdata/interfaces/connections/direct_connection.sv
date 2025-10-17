// Direct interface connections between modules
interface data_intf;
  logic [15:0] data;
  logic valid;
endinterface

module source(data_intf out);
  always_comb begin
    out.data = 16'hABCD;
    out.valid = 1'b1;
  end
endmodule

module sink(data_intf in);
  logic [15:0] captured;
  
  always_comb begin
    if (in.valid) begin
      captured = in.data;
    end
  end
endmodule

module top;
  data_intf channel();
  
  source src(.out(channel));
  sink snk(.in(channel));
endmodule

