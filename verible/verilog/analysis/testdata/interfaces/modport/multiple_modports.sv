// Interface with multiple modports for different roles
interface multi_modport_intf;
  logic clk;
  logic [31:0] addr;
  logic [63:0] data_write;
  logic [63:0] data_read;
  logic write_en;
  logic read_en;
  logic ack;
  
  // CPU modport
  modport cpu (
    input  clk,
    output addr,
    output data_write,
    input  data_read,
    output write_en,
    output read_en,
    input  ack
  );
  
  // Memory modport
  modport memory (
    input  clk,
    input  addr,
    input  data_write,
    output data_read,
    input  write_en,
    input  read_en,
    output ack
  );
  
  // Monitor modport (for debugging)
  modport monitor (
    input clk,
    input addr,
    input data_write,
    input data_read,
    input write_en,
    input read_en,
    input ack
  );
endinterface

module cpu_unit(multi_modport_intf.cpu cpu);
  always_ff @(posedge cpu.clk) begin
    cpu.addr <= cpu.addr + 4;
    cpu.write_en <= 1'b1;
  end
endmodule

module memory_unit(multi_modport_intf.memory mem);
  logic [63:0] storage[0:1023];
  
  always_ff @(posedge mem.clk) begin
    if (mem.write_en) begin
      storage[mem.addr[11:3]] <= mem.data_write;
      mem.ack <= 1'b1;
    end
  end
endmodule

module monitor_unit(multi_modport_intf.monitor mon);
  always_ff @(posedge mon.clk) begin
    if (mon.write_en) begin
      $display("Write: addr=%h, data=%h", mon.addr, mon.data_write);
    end
  end
endmodule

module top;
  multi_modport_intf bus();
  
  cpu_unit cpu(.cpu(bus));
  memory_unit mem(.mem(bus));
  monitor_unit mon(.mon(bus));
endmodule

