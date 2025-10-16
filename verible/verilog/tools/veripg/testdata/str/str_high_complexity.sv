// Test file for STR_002: Module exceeds complexity threshold (50+ statements)

module str_high_complexity(
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);
  // Violation: Too many statements - should be refactored into smaller modules
  logic [7:0] r0, r1, r2, r3, r4, r5, r6, r7, r8, r9;
  logic [7:0] r10, r11, r12, r13, r14, r15, r16, r17, r18, r19;
  logic [7:0] r20, r21, r22, r23, r24, r25, r26, r27, r28, r29;
  logic [7:0] r30, r31, r32, r33, r34, r35, r36, r37, r38, r39;
  logic [7:0] r40, r41, r42, r43, r44, r45, r46, r47, r48, r49;
  logic [7:0] r50, r51, r52, r53, r54, r55;  // 56 registers = high complexity
  
  always_ff @(posedge clk) begin
    r0 <= data_in; r1 <= r0; r2 <= r1; r3 <= r2; r4 <= r3;
    r5 <= r4; r6 <= r5; r7 <= r6; r8 <= r7; r9 <= r8;
    r10 <= r9; r11 <= r10; r12 <= r11; r13 <= r12; r14 <= r13;
    r15 <= r14; r16 <= r15; r17 <= r16; r18 <= r17; r19 <= r18;
    r20 <= r19; r21 <= r20; r22 <= r21; r23 <= r22; r24 <= r23;
    r25 <= r24; r26 <= r25; r27 <= r26; r28 <= r27; r29 <= r28;
    r30 <= r29; r31 <= r30; r32 <= r31; r33 <= r32; r34 <= r33;
    r35 <= r34; r36 <= r35; r37 <= r36; r38 <= r37; r39 <= r38;
    r40 <= r39; r41 <= r40; r42 <= r41; r43 <= r42; r44 <= r43;
    r45 <= r44; r46 <= r45; r47 <= r46; r48 <= r47; r49 <= r48;
    r50 <= r49; r51 <= r50; r52 <= r51; r53 <= r52; r54 <= r53;
    r55 <= r54; data_out <= r55;  // 56 assignments
  end
endmodule

