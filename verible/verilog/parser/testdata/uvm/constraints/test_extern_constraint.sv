// UVM Constraint Test: Extern constraint with distribution operators
// Tests out-of-body constraint definitions with soft modifier and dist operator
// Phase 1.2 - Fixture 2

class test_constraints;
  rand int unsigned delay;
  rand int unsigned timeout;
  
  extern constraint delay_c;
  extern constraint timeout_c;
endclass

// Out-of-body constraint definition with distribution
constraint test_constraints::delay_c {
  soft delay dist {0 := 5, [1:10] :/ 5};
}

// Out-of-body constraint with implication
constraint test_constraints::timeout_c {
  delay > 0 -> timeout inside {[10:100]};
}

