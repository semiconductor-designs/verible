// UVM Type Parameter Test: Parameterized classes with type parameters
// Tests type keyword in parameter lists and type parameter inheritance
// Phase 1.2 - Fixture 3

// Base class with type parameter
class base_class #(type T = int);
  T data;
  
  function new();
    data = '0;
  endfunction
endclass

// Derived class with type parameter passed to base
class derived_class #(type CFG_T = base_cfg) 
  extends base_class#(CFG_T);
  
  CFG_T config;
  
  function new();
    super.new();
  endfunction
endclass

// Multiple type parameters
class multi_param_class #(
  type T1 = int,
  type T2 = bit,
  type T3 = logic
);
  T1 field1;
  T2 field2;
  T3 field3;
endclass

// Placeholder for base_cfg type
class base_cfg;
endclass

