// UVM Macro Test: Basic uvm_object_utils pattern
// Tests UVM object registration macros with field automation
// Phase 1.2 - Fixture 1

class simple_item extends uvm_sequence_item;
  rand bit data;
  
  `uvm_object_utils_begin(simple_item)
    `uvm_field_int(data, UVM_DEFAULT)
  `uvm_object_utils_end
  
  function new(string name = "simple_item");
    super.new(name);
  endfunction
endclass

