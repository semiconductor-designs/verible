// Basic class inheritance test
// Purpose: Test simple extends keyword and inheritance

class BaseClass;
  int base_value;
  
  function new(int val);
    base_value = val;
  endfunction
  
  function int get_value();
    return base_value;
  endfunction
endclass

class DerivedClass extends BaseClass;
  int derived_value;
  
  function new(int base_val, int deriv_val);
    super.new(base_val);
    derived_value = deriv_val;
  endfunction
  
  function int get_total();
    return base_value + derived_value;
  endfunction
endclass

module test_class_hierarchy;
  initial begin
    DerivedClass obj;
    obj = new(10, 20);
    $display("Base value: %0d", obj.get_value());
    $display("Total value: %0d", obj.get_total());
  end
endmodule

