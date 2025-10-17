// Parametric class inheritance test
// Purpose: Test parameterized class inheritance

class BaseQueue #(parameter int WIDTH = 8);
  typedef logic [WIDTH-1:0] data_t;
  data_t queue[$];
  
  function void push(data_t item);
    queue.push_back(item);
  endfunction
  
  function data_t pop();
    return queue.pop_front();
  endfunction
  
  function int size();
    return queue.size();
  endfunction
endclass

class PriorityQueue #(parameter int WIDTH = 8) extends BaseQueue#(WIDTH);
  typedef logic [WIDTH-1:0] data_t;
  int priorities[$];
  
  function void push_with_priority(data_t item, int priority);
    int insert_pos = 0;
    
    // Find insertion position based on priority
    for (int i = 0; i < priorities.size(); i++) begin
      if (priority > priorities[i]) begin
        insert_pos = i;
        break;
      end
    end
    
    // Insert at position
    queue.insert(insert_pos, item);
    priorities.insert(insert_pos, priority);
  endfunction
  
  function data_t pop();
    if (priorities.size() > 0)
      void'(priorities.pop_front());
    return super.pop();
  endfunction
endclass

module test_parametric_inheritance;
  initial begin
    PriorityQueue#(16) pq;
    pq = new();
    
    pq.push_with_priority(16'hAAAA, 10);
    pq.push_with_priority(16'hBBBB, 20);
    pq.push_with_priority(16'hCCCC, 15);
    
    $display("Size: %0d", pq.size());
    $display("Pop: %0h", pq.pop());  // Should be BBBB (priority 20)
  end
endmodule

