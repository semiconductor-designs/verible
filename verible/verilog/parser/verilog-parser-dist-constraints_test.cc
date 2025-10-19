// Copyright 2025
// Verible UVM Enhancement - Distribution Constraint Tests
// Week 12: Phase 3.2 - Distribution constraint detailed testing

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

// DEFERRED TEST FROM WEEK 11: Out-of-body dist constraint
TEST(DistConstraints, OutOfBodyDistConstraint) {
  const char* code = R"(
class weighted_item;
  int myval;
  extern constraint myval_c;
endclass

constraint weighted_item::myval_c {
  myval dist {
    0 := 50,
    [1:5] := 30,
    [6:10] :/ 20
  };
}
)";
  
  // This was deferred from Week 11 - testing out-of-body dist constraint
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Out-of-body distribution constraint should parse";
}

// Week 12 Test 2: Single value with := weight
TEST(DistConstraints, SingleValueEqualWeight) {
  const char* code = R"(
class test_class;
  int value;
  constraint value_c {
    value dist {
      0 := 100
    };
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Single value with := weight should parse";
}

// Week 12 Test 3: Single value with :/ weight
TEST(DistConstraints, SingleValueDivideWeight) {
  const char* code = R"(
class test_class;
  int value;
  constraint value_c {
    value dist {
      0 :/ 100
    };
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Single value with :/ weight should parse";
}

// Week 12 Test 4: Range with := weight
TEST(DistConstraints, RangeEqualWeight) {
  const char* code = R"(
class test_class;
  int value;
  constraint value_c {
    value dist {
      [0:10] := 50
    };
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Range with := weight should parse";
}

// Week 12 Test 5: Range with :/ weight
TEST(DistConstraints, RangeDivideWeight) {
  const char* code = R"(
class test_class;
  int value;
  constraint value_c {
    value dist {
      [0:10] :/ 50
    };
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Range with :/ weight should parse";
}

// Week 12 Test 6: Mixed single values and ranges
TEST(DistConstraints, MixedValuesAndRanges) {
  const char* code = R"(
class test_class;
  int value;
  constraint value_c {
    value dist {
      0 := 10,
      [1:5] := 30,
      10 := 20,
      [20:30] :/ 40
    };
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Mixed single values and ranges should parse";
}

// Week 12 Test 7: Multiple dist constraints in same class
TEST(DistConstraints, MultipleDistConstraints) {
  const char* code = R"(
class test_class;
  int addr;
  int data;
  
  constraint addr_c {
    addr dist {
      0 := 50,
      [1:100] :/ 50
    };
  }
  
  constraint data_c {
    data dist {
      [0:255] :/ 100
    };
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Multiple dist constraints should parse";
}

// Week 12 Test 8: Dist constraint with large ranges
TEST(DistConstraints, LargeRanges) {
  const char* code = R"(
class test_class;
  int value;
  constraint value_c {
    value dist {
      [0:1000] := 25,
      [1001:2000] := 25,
      [2001:3000] := 25,
      [3001:4000] := 25
    };
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Dist constraint with large ranges should parse";
}

// Week 12 Test 9: Dist constraint with hex values
TEST(DistConstraints, HexValues) {
  const char* code = R"(
class test_class;
  bit [7:0] value;
  constraint value_c {
    value dist {
      8'h00 := 10,
      [8'h01:8'h7F] :/ 80,
      8'hFF := 10
    };
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Dist constraint with hex values should parse";
}

// Week 12 Test 10: Dist with negative values
TEST(DistConstraints, NegativeValues) {
  const char* code = R"(
class test_class;
  int signed_value;
  constraint signed_value_c {
    signed_value dist {
      [-100:-1] := 25,
      0 := 50,
      [1:100] := 25
    };
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Dist constraint with negative values should parse";
}

// Week 12 Test 11: Dist constraint combined with other constraint expressions
TEST(DistConstraints, DistWithOtherConstraints) {
  const char* code = R"(
class test_class;
  int value;
  int max_val;
  
  constraint value_c {
    value dist {
      [0:50] := 70,
      [51:100] := 30
    };
    value < max_val;
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Dist constraint combined with other constraints should parse";
}

// Week 12 Test 12: Dist constraint with only :/ weights
TEST(DistConstraints, OnlyDivideWeights) {
  const char* code = R"(
class test_class;
  int value;
  constraint value_c {
    value dist {
      [0:25] :/ 1,
      [26:50] :/ 1,
      [51:75] :/ 1,
      [76:100] :/ 1
    };
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Dist constraint with only :/ weights should parse";
}

// Week 12 Test 13: Dist constraint with only := weights
TEST(DistConstraints, OnlyEqualWeights) {
  const char* code = R"(
class test_class;
  int value;
  constraint value_c {
    value dist {
      0 := 25,
      1 := 25,
      2 := 25,
      3 := 25
    };
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Dist constraint with only := weights should parse";
}

// Week 12 Test 14: Nested constraint with dist (inside if block)
TEST(DistConstraints, DistInsideConditional) {
  const char* code = R"(
class test_class;
  bit enable;
  int value;
  
  constraint value_c {
    if (enable) {
      value dist {
        0 := 50,
        [1:10] :/ 50
      };
    }
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Dist constraint inside conditional should parse";
}

// Week 12 Test 15: Dist constraint in parameterized class
TEST(DistConstraints, DistInParameterizedClass) {
  const char* code = R"(
class test_class #(int MAX_VAL = 100);
  int value;
  
  constraint value_c {
    value dist {
      0 := 10,
      [1:10] := 90
    };
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Dist constraint in parameterized class should parse";
}

}  // namespace
}  // namespace verilog
