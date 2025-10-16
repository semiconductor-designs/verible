// Test file for STR_006: Instantiation without named ports

module sub_module(
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) data_out <= 8'h00;
    else data_out <= data_in;
  end
endmodule

module str_unnamed_ports(
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);
  // Violation: Positional port connection instead of named
  sub_module u1(clk, rst_n, data_in, data_out);  // Should use .clk(clk), .rst_n(rst_n), etc.
  
  // Correct way:
  // sub_module u2(
  //   .clk(clk),
  //   .rst_n(rst_n),
  //   .data_in(data_in),
  //   .data_out(data_out)
  // );
endmodule

