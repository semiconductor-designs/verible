// UVM Distribution Constraint Test: Distribution operators and weights
// Tests dist operator with := (per-value) and :/ (per-range) weights
// Phase 1.2 - Fixture 4

class test_dist;
  rand int delay;
  rand int size;
  rand int mode;
  
  // Distribution with per-value and per-range weights
  constraint delay_c {
    delay dist {
      0       := 50,    // 50 weight for value 0
      [1:10]  := 40,    // 40 weight distributed across range
      [11:20] :/ 10     // 10 weight total across range
    };
  }
  
  // Inside operator with sets
  constraint size_c {
    size inside {[1:4], [8:16], 32, 64};
  }
  
  // Implication and bidirectional implication
  constraint mode_c {
    mode == 0 -> delay < 5;
    mode == 1 <-> (delay inside {[10:20]});
  }
  
  // Solve-before ordering
  constraint order_c {
    solve mode before delay;
  }
endclass

