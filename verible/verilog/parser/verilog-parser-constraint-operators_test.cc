// Copyright 2025
// Verible UVM Enhancement - Advanced Constraint Operators Tests
// Week 13-14: Phase 3.3-3.4 - inside, solve...before, implication

#include "gtest/gtest.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Helper function to parse SystemVerilog code
bool ParsesSuccessfully(const char* code) {
  VerilogAnalyzer analyzer(code, "test.sv");
  const auto status = analyzer.Analyze();
  return status.ok() && analyzer.SyntaxTree() != nullptr;
}

// ========== INSIDE OPERATOR TESTS (Week 13) ==========

// Week 13 Test 1: Basic inside operator with set
TEST(ConstraintOperators, InsideOperatorSet) {
  const char* code = R"(
class test_class;
  int value;
  constraint value_c {
    value inside {0, 1, 2, 3};
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "inside operator with set should parse";
}

// Week 13 Test 2: inside operator with range
TEST(ConstraintOperators, InsideOperatorRange) {
  const char* code = R"(
class test_class;
  int value;
  constraint value_c {
    value inside {[0:10], [20:30]};
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "inside operator with ranges should parse";
}

// Week 13 Test 3: inside operator with mixed values and ranges
TEST(ConstraintOperators, InsideOperatorMixed) {
  const char* code = R"(
class test_class;
  int value;
  constraint value_c {
    value inside {0, [1:5], 10, [20:30]};
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "inside operator with mixed values and ranges should parse";
}

// Week 13 Test 4: Negated inside operator
TEST(ConstraintOperators, InsideOperatorNegated) {
  const char* code = R"(
class test_class;
  int value;
  constraint value_c {
    !(value inside {[0:10]});
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Negated inside operator should parse";
}

// Week 13 Test 5: inside operator in extern constraint
TEST(ConstraintOperators, InsideOperatorExtern) {
  const char* code = R"(
class test_class;
  int addr;
  extern constraint addr_c;
endclass

constraint test_class::addr_c {
  addr inside {[0:255]};
}
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "inside operator in extern constraint should parse";
}

// ========== SOLVE...BEFORE TESTS (Week 13) ==========

// Week 13 Test 6: Basic solve...before
TEST(ConstraintOperators, SolveBefore) {
  const char* code = R"(
class test_class;
  int a, b;
  constraint order_c {
    solve a before b;
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "solve...before should parse";
}

// Week 13 Test 7: Multiple solve...before statements
TEST(ConstraintOperators, MultipleSolveBefore) {
  const char* code = R"(
class test_class;
  int a, b, c;
  constraint order_c {
    solve a before b;
    solve b before c;
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Multiple solve...before statements should parse";
}

// Week 13 Test 8: solve...before in extern constraint
TEST(ConstraintOperators, SolveBeforeExtern) {
  const char* code = R"(
class test_class;
  int x, y;
  extern constraint xy_c;
endclass

constraint test_class::xy_c {
  solve x before y;
  x > 0;
  y == x * 2;
}
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "solve...before in extern constraint should parse";
}

// ========== IMPLICATION OPERATOR TESTS (Week 14) ==========

// Week 14 Test 9: Basic implication (->)
TEST(ConstraintOperators, ImplicationOperator) {
  const char* code = R"(
class test_class;
  bit enable;
  int value;
  constraint enable_c {
    enable -> (value > 0);
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Implication operator (->) should parse";
}

// Week 14 Test 10: Bi-directional implication (<->)
TEST(ConstraintOperators, BiImplicationOperator) {
  const char* code = R"(
class test_class;
  bit flag_a;
  bit flag_b;
  constraint mutual_c {
    flag_a <-> flag_b;
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Bi-directional implication (<->) should parse";
}

// Week 14 Test 11: Nested implications
TEST(ConstraintOperators, NestedImplications) {
  const char* code = R"(
class test_class;
  bit mode1, mode2;
  int value;
  constraint mode_c {
    mode1 -> (mode2 -> (value < 100));
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Nested implications should parse";
}

// Week 14 Test 12: Implication with inside
TEST(ConstraintOperators, ImplicationWithInside) {
  const char* code = R"(
class test_class;
  bit valid;
  int addr;
  constraint valid_addr_c {
    valid -> (addr inside {[0:255]});
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Implication with inside operator should parse";
}

// ========== COMBINED OPERATOR TESTS (Week 14) ==========

// Week 14 Test 13: All operators combined
TEST(ConstraintOperators, AllOperatorsCombined) {
  const char* code = R"(
class test_class;
  bit enable;
  int addr, data;
  
  constraint complex_c {
    solve addr before data;
    enable -> (addr inside {[0:100]});
    addr inside {[0:255]};
    data dist {0 := 50, [1:10] :/ 50};
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "All constraint operators combined should parse";
}

// Week 14 Test 14: Operators in extern constraint with soft
TEST(ConstraintOperators, OperatorsWithSoftExtern) {
  const char* code = R"(
class test_class;
  bit mode;
  int value;
  extern constraint mode_value_c;
endclass

constraint test_class::mode_value_c {
  soft value inside {[0:100]};
  mode -> (value > 50);
}
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Operators with soft in extern constraint should parse";
}

// Week 14 Test 15: Complex constraint expression
TEST(ConstraintOperators, ComplexConstraintExpression) {
  const char* code = R"(
class test_class;
  int a, b, c;
  bit flag;
  
  constraint complex_expr_c {
    solve a before b;
    solve b before c;
    flag -> (a inside {[0:10]});
    !flag -> (a inside {[11:20]});
    b == a * 2;
    c inside {b, b+1, b+2};
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Complex constraint expression should parse";
}

}  // namespace
}  // namespace verilog

