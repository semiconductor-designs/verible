// UVM Complex Macro Test: Nested macros and code blocks as arguments
// Tests macro calls inside macro arguments and code block arguments
// Phase 1.2 - Fixture 5

// Define macro that takes a statement/code block as argument
`define LOOP_BODY(stmt) \
  fork \
    begin \
      stmt \
    end \
  join_none

// Define macro that uses another macro
`define NESTED_LOOP(inner_stmt) \
  foreach (items[i]) begin \
    `LOOP_BODY(inner_stmt) \
  end

// Usage: Macro call inside macro argument
module test_macro_nesting;
  int items[4];
  
  initial begin
    // Simple case: code block as macro argument
    `LOOP_BODY(
      $display("Test message")
    )
    
    // Complex case: UVM macro inside custom macro
    `LOOP_BODY(
      `uvm_info("TEST", "Nested macro call", UVM_LOW)
    )
    
    // Triple nesting
    `NESTED_LOOP(
      `uvm_info("LOOP", $sformatf("Item %0d", i), UVM_MEDIUM)
    )
  end
endmodule

