// Copyright 2025 The Verible Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Tests for bind directive (M5 Group 3)
// Verifies existing grammar implementation

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Basic bind directive tests - based on existing parser_test.cc examples
TEST(VerilogParserBindTest, SimpleBindModule) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind scope_x type_y z(.*); package p; endpackage\n", 0);
}

TEST(VerilogParserBindTest, SimpleBindMultipleInstances) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind scope_x type_y z1(.*), z2(.*); package p; endpackage\n", 1);
}

// With target instance list (colon syntax)
TEST(VerilogParserBindTest, BindWithTargetList) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind module_scope : inst_x type_y inst_z(.*); package p; endpackage\n", 2);
}

TEST(VerilogParserBindTest, BindWithMultipleTargets) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind module_scope : inst_x1, inst_x2 type_y inst_z(.*); package p; endpackage\n", 3);
}

// With scope resolution
TEST(VerilogParserBindTest, BindWithScopeResolution) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind module_scope : inst_x type_y::a inst_z(.*); package p; endpackage\n", 4);
}

// Parameterized types
TEST(VerilogParserBindTest, BindParameterizedType) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind module_scope : inst_x type_y::a#(4,3) inst_z(.*); package p; endpackage\n", 5);
}

// Hierarchical targets
TEST(VerilogParserBindTest, BindHierarchicalTargets) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind module_scope : inst_x1.www, inst_x2.zz[0] type_y inst_z(.*); package p; endpackage\n", 6);
}

// Multiple instances with hierarchical targets
TEST(VerilogParserBindTest, BindHierarchicalMultipleInst) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind module_scope : inst_x1.www, inst_x2.zz[0] type_y z1(.*), z2(.*); package p; endpackage\n", 7);
}

// Inside module context (from module tests)
TEST(VerilogParserBindTest, BindInsideModule) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module bind_me; bind dut.rtl.mm ib_if ib_if_inst(); endmodule\n", 8);
}

TEST(VerilogParserBindTest, BindInsideModuleWithPorts) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module bind_me; bind dut.rtl.ff tc_c tc_c_inst(.clk(clk_tc), .*); endmodule\n", 9);
}

// Different port connection styles
TEST(VerilogParserBindTest, BindWildcardPorts) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind cpu checker_type inst(.*); package p; endpackage\n", 10);
}

TEST(VerilogParserBindTest, BindNamedPorts) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind cpu checker_type inst(.clk(clk), .rst(rst_n)); package p; endpackage\n", 11);
}

TEST(VerilogParserBindTest, BindMixedPorts) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind cpu checker_type inst(.clk(clk), .*); package p; endpackage\n", 12);
}

TEST(VerilogParserBindTest, BindEmptyPorts) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind cpu checker_type inst(); package p; endpackage\n", 13);
}

// Hierarchical scopes
TEST(VerilogParserBindTest, BindHierarchicalScope) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind top.mid.bottom checker_type inst(.*); package p; endpackage\n", 14);
}

// With array indexing
TEST(VerilogParserBindTest, BindWithArrayIndex) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind sys : cpu[0] checker_type inst(.*); package p; endpackage\n", 15);
}

TEST(VerilogParserBindTest, BindWithMultiDimArray) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind sys : cpu[0][1] checker_type inst(.*); package p; endpackage\n", 16);
}

// Complex real-world patterns
TEST(VerilogParserBindTest, BindComplexMultiTarget) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind top : inst1, inst2 checker_type chk(.*); package p; endpackage\n", 17);
}

TEST(VerilogParserBindTest, BindInterfacePattern) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind axi_bus axi_if#(32,4) if_inst(.aclk(clk)); package p; endpackage\n", 18);
}

TEST(VerilogParserBindTest, BindProgramPattern) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "bind testbench test_prog prog_inst(); package p; endpackage\n", 19);
}

}  // namespace
}  // namespace verilog

