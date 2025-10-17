// Invalid method override error test
// Purpose: Test detection of incompatible method overrides

class BaseClass;
  int base_value;
  
  function new(int val);
    base_value = val;
  endfunction
  
  virtual function int calculate(int x, int y);
    return x + y;
  endfunction
  
  virtual function void display();
    $display("Base value: %0d", base_value);
  endfunction
endclass

class DerivedClass extends BaseClass;
  int derived_value;
  
  function new(int val);
    super.new(val);
    derived_value = val * 2;
  endfunction
  
  // ERROR: Signature mismatch - different number of parameters
  virtual function int calculate(int x);  // Should have 2 params like base
    return x + derived_value;
  endfunction
  
  // ERROR: Return type mismatch
  virtual function string display();  // Should be void like base
    return $sformatf("Derived value: %0d", derived_value);
  endfunction
endclass

module test_override_errors;
  // Expected errors:
  // 1. "Method 'calculate' signature mismatch: expected 2 parameters, got 1"
  // 2. "Method 'display' return type mismatch: expected void, got string"
  initial begin
    DerivedClass obj;
    obj = new(10);
    obj.display();
  end
endmodule

