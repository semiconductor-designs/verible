// Array of interfaces
interface channel_intf;
  logic [7:0] data;
  logic valid;
endinterface

module multi_channel_device(
  channel_intf.master ch[4]
);
  genvar i;
  generate
    for (i = 0; i < 4; i++) begin : gen_channels
      always_comb begin
        ch[i].data = 8'(i);
        ch[i].valid = 1'b1;
      end
    end
  endgenerate
  
  modport master (output data, output valid);
endmodule

module top;
  channel_intf channels[4]();
  
  multi_channel_device dev(.ch(channels));
endmodule

