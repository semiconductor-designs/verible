// Multiple inheritance levels test
// Purpose: Test chain of inheritance (A -> B -> C)

class GrandParent;
  int grand_value;
  
  function new(int val);
    grand_value = val;
  endfunction
  
  function int get_grand();
    return grand_value;
  endfunction
endclass

class Parent extends GrandParent;
  int parent_value;
  
  function new(int grand_val, int parent_val);
    super.new(grand_val);
    parent_value = parent_val;
  endfunction
  
  function int get_parent();
    return parent_value;
  endfunction
endclass

class Child extends Parent;
  int child_value;
  
  function new(int grand_val, int parent_val, int child_val);
    super.new(grand_val, parent_val);
    child_value = child_val;
  endfunction
  
  function int get_all();
    return grand_value + parent_value + child_value;
  endfunction
endclass

module test_multiple_inheritance;
  initial begin
    Child obj;
    obj = new(10, 20, 30);
    $display("Grand: %0d", obj.get_grand());
    $display("Parent: %0d", obj.get_parent());
    $display("Total: %0d", obj.get_all());
  end
endmodule

