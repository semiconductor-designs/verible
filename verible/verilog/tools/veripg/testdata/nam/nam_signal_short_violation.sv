// Test case for NAM_002: Signal names too short/non-descriptive
module nam_signal_short_violation;
  logic a;      // NAM_002: Too short (1 char)
  logic b;      // NAM_002: Too short
  logic x1;     // NAM_002: Non-descriptive
  
  logic data;   // OK: descriptive enough (4+ chars)
  logic counter; // OK: descriptive
endmodule

