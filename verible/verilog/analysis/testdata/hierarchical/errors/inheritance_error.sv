// Circular inheritance error test
// Purpose: Test detection of circular class inheritance

// ERROR: Circular inheritance A -> B -> C -> A
class ClassA extends ClassC;
  int value_a;
  
  function new(int val);
    value_a = val;
  endfunction
endclass

class ClassB extends ClassA;
  int value_b;
  
  function new(int val);
    super.new(val);
    value_b = val * 2;
  endfunction
endclass

class ClassC extends ClassB;
  int value_c;
  
  function new(int val);
    super.new(val);
    value_c = val * 3;
  endfunction
endclass

module test_circular_inheritance;
  // This should be caught by HierarchicalTypeChecker
  // Expected error: "Circular inheritance detected: ClassA -> ClassC -> ClassB -> ClassA"
  initial begin
    ClassA obj;
    // This will never work due to circular inheritance
    obj = new(10);
  end
endmodule

