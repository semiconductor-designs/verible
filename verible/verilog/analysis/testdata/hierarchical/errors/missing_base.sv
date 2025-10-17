// Missing base class error test
// Purpose: Test detection of undefined base class

// ERROR: BaseClass is not defined
class DerivedClass extends BaseClass;
  int derived_value;
  
  function new(int val);
    super.new(val);  // ERROR: super refers to undefined BaseClass
    derived_value = val;
  endfunction
  
  function int get_value();
    return derived_value;
  endfunction
endclass

// ERROR: UndefinedInterface is not defined
interface ExtendedInterface (input logic clk) extends UndefinedInterface;
  logic data;
  logic valid;
  
  modport master (
    output data,
    output valid
  );
endinterface

module test_missing_base;
  // Expected errors:
  // 1. "Base class 'BaseClass' not found for 'DerivedClass'"
  // 2. "Base interface 'UndefinedInterface' not found for 'ExtendedInterface'"
  initial begin
    DerivedClass obj;
    obj = new(42);
  end
endmodule

