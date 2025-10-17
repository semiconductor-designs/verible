# Test Failures Analysis - Path to 100%

**Date**: October 17, 2025  
**Current Status**: 92% (65/71 tests passing)  
**Target**: 100% (71/71 tests passing)  
**Philosophy**: No hurry, no skip, 100%

---

## Executive Summary

We have **6 failing tests** across 2 components preventing us from achieving 100%:

1. **CallGraphEnhancer**: 2 failures (31/33 = 94%)
2. **DataFlowAnalyzer**: 4 failures (13/17 = 76%)
3. **EnhancedUnusedDetector**: 0 failures (21/21 = 100%) ✅

All failures are **fixable** and represent incomplete implementation, not fundamental design flaws.

---

## Detailed Analysis

### Component 1: CallGraphEnhancer - 2 Failures

#### Failure 1: `CallDepthComputation` ❌

**Location**: `call-graph-enhancer_test.cc:802-803`

**Error**:
```
Value of: level2->call_depth >= level1->call_depth
  Actual: false
Expected: true

Value of: level1->call_depth >= level0->call_depth
  Actual: false
Expected: true
```

**Root Cause**: BFS-based depth computation doesn't correctly handle multi-path graphs

**Current Implementation** (`call-graph-enhancer.cc`):
```cpp
void CallGraphEnhancer::ComputeDepthBFS(CallGraphNode* entry_point) {
  std::queue<CallGraphNode*> queue;
  queue.push(entry_point);
  
  while (!queue.empty()) {
    auto* node = queue.front();
    queue.pop();
    
    for (auto* callee : node->callees) {
      int new_depth = node->call_depth + 1;
      if (new_depth > callee->call_depth) {  // Takes maximum
        callee->call_depth = new_depth;
        queue.push(callee);
      }
    }
  }
}
```

**Problem**: 
- Algorithm visits nodes in BFS order
- If a shorter path is encountered first, it sets a lower depth
- Later longer paths update the depth, but parent relationships may already be computed
- The depth comparison in the test expects monotonically increasing depths along one specific path

**Test Code**:
```cpp
// Test expects: level0 < level1 < level2
// But BFS may visit level2 before level1 in some orderings
auto* level0 = enhancer.GetNode("level0");
auto* level1 = enhancer.GetNode("level1");
auto* level2 = enhancer.GetNode("level2");
EXPECT_GE(level2->call_depth, level1->call_depth);
EXPECT_GE(level1->call_depth, level0->call_depth);
```

**Solution Options**:

**Option A: Fix BFS Algorithm** (30-45 min)
```cpp
void CallGraphEnhancer::ComputeDepthBFS(CallGraphNode* entry_point) {
  std::queue<CallGraphNode*> queue;
  std::set<CallGraphNode*> visited;
  
  entry_point->call_depth = 0;
  queue.push(entry_point);
  visited.insert(entry_point);
  
  while (!queue.empty()) {
    auto* node = queue.front();
    queue.pop();
    
    for (auto* callee : node->callees) {
      int new_depth = node->call_depth + 1;
      
      // Always update to maximum depth (longest path)
      if (new_depth > callee->call_depth) {
        callee->call_depth = new_depth;
        
        // Re-visit if depth changed to propagate deeper
        if (visited.find(callee) != visited.end()) {
          queue.push(callee);
        }
      }
      
      if (visited.find(callee) == visited.end()) {
        queue.push(callee);
        visited.insert(callee);
      }
    }
  }
}
```

**Option B: Use Topological Sort + Dynamic Programming** (1-2 hours)
```cpp
void CallGraphEnhancer::ComputeCallDepths() {
  // Step 1: Topological sort of DAG (excluding back edges)
  std::vector<CallGraphNode*> sorted = TopologicalSort();
  
  // Step 2: DP to compute longest path (depth)
  for (auto* node : sorted) {
    for (auto* callee : node->callees) {
      if (!IsBackEdge(node, callee)) {
        callee->call_depth = std::max(callee->call_depth, 
                                      node->call_depth + 1);
      }
    }
  }
}
```

**Recommendation**: **Option A** - Fix BFS with re-visitation (30-45 min)
- Simpler, less code change
- Handles cycles correctly (already detected separately)
- Maintains current architecture

---

#### Failure 2: `UnreachableFunctionDetection` ❌

**Location**: `call-graph-enhancer_test.cc:867`

**Error**:
```
Value of: orphan->is_unreachable
  Actual: false
Expected: true
```

**Root Cause**: Classification logic treats all functions with no callers as entry points, not distinguishing truly unreachable (orphan) functions

**Current Implementation** (`call-graph-enhancer.cc`):
```cpp
void CallGraphEnhancer::FindUnreachableFunctions() {
  for (const auto& node : nodes_) {
    if (node->callers.empty() && !node->is_entry_point && !node->is_dpi) {
      node->is_unreachable = true;
      statistics_.unreachable_functions++;
    }
  }
}

// But earlier in IdentifyEntryPoints():
void CallGraphEnhancer::IdentifyEntryPoints() {
  for (const auto& node : nodes_) {
    if (node->callers.empty()) {
      node->is_entry_point = true;  // ← This marks ALL uncalled functions
      statistics_.entry_points++;
    }
  }
}
```

**Problem**: 
- `IdentifyEntryPoints()` marks **all** functions with no callers as entry points
- `FindUnreachableFunctions()` then checks `!node->is_entry_point`
- Result: Orphan functions are marked as entry points instead of unreachable

**Test Code**:
```cpp
// orphan() has no callers, should be unreachable
// But currently marked as entry_point instead
auto* orphan = enhancer.GetNode("orphan");
EXPECT_TRUE(orphan->is_unreachable);  // FAILS
```

**Solution** (30 min):

**Option A: Heuristic-based Classification**
```cpp
void CallGraphEnhancer::IdentifyEntryPoints() {
  for (const auto& node : nodes_) {
    if (node->callers.empty()) {
      // Heuristic: Top-level (module scope) functions are entry points
      // Local/nested functions with no callers are likely unreachable
      if (IsModuleLevel(node.get()) || HasPublicScope(node.get())) {
        node->is_entry_point = true;
        statistics_.entry_points++;
      }
    }
  }
}

void CallGraphEnhancer::FindUnreachableFunctions() {
  for (const auto& node : nodes_) {
    // Unreachable if: no callers AND not entry point AND not DPI
    if (node->callers.empty() && !node->is_entry_point && !node->is_dpi) {
      node->is_unreachable = true;
      statistics_.unreachable_functions++;
    }
  }
}
```

**Option B: Explicit Entry Point Marking** (simpler)
```cpp
// Change IdentifyEntryPoints() to NOT automatically mark all no-caller functions
void CallGraphEnhancer::IdentifyEntryPoints() {
  // Only mark explicitly identified entry points (e.g., DPI, top-level)
  for (const auto& node : nodes_) {
    if (node->is_dpi || IsTopLevel(node.get())) {
      node->is_entry_point = true;
      statistics_.entry_points++;
    }
  }
}

void CallGraphEnhancer::FindUnreachableFunctions() {
  for (const auto& node : nodes_) {
    // Unreachable if: no callers AND not explicitly marked as entry point
    if (node->callers.empty() && !node->is_entry_point) {
      node->is_unreachable = true;
      statistics_.unreachable_functions++;
    }
  }
}
```

**Recommendation**: **Option B** - Explicit entry point marking (30 min)
- Clearer semantics
- User can explicitly mark entry points if needed
- Orphan functions correctly identified as unreachable

---

### Component 2: DataFlowAnalyzer - 4 Failures

#### Overview
All 4 failures relate to **parameter analysis** - a feature that was intentionally stubbed/deferred in Week 10.

#### Failure 1: `ParameterExtraction` ❌
**Root Cause**: Parameter nodes extracted but not analyzed for constant values

#### Failure 2: `ParameterIsConstant` ❌
**Root Cause**: No constant propagation logic implemented

#### Failure 3: `ConstantPropagation` ❌
**Root Cause**: No constant value tracking across assignments

#### Failure 4: `FullAnalysis` ❌
**Root Cause**: Missing parameter and constant analysis

**Current Status** (`data-flow-analyzer.cc`):
```cpp
void DataFlowAnalyzer::ExtractParameters(const SymbolTableNode& node, 
                                         const std::string& scope) {
  // Basic extraction implemented
  DataFlowNode df_node;
  df_node.name = name;
  df_node.type = DataFlowNode::kParameter;
  df_node.fully_qualified_name = fqn;
  // ... basic fields populated ...
  
  data_flow_graph_.nodes.push_back(df_node);
  
  // ❌ TODO: Extract parameter value (constant expression)
  // ❌ TODO: Mark as constant
  // ❌ TODO: Propagate to uses
}
```

**Missing Features**:
1. Constant expression evaluation
2. Parameter value extraction from CST
3. Constant propagation analysis
4. Data flow edges for parameters

**Solution** (2-3 hours for complete implementation):

**Step 1: Extract Parameter Values from CST** (45 min)
```cpp
void DataFlowAnalyzer::ExtractParameterValue(DataFlowNode& param_node,
                                             const verible::Symbol& param_decl) {
  // Use Verible CST APIs to extract parameter value
  const auto* value_expr = GetParameterAssignExpression(param_decl);
  if (!value_expr) {
    param_node.is_constant = false;
    return;
  }
  
  // Try to evaluate constant expression
  auto result = EvaluateConstantExpression(*value_expr);
  if (result.has_value()) {
    param_node.is_constant = true;
    param_node.constant_value = result.value();
  }
}
```

**Step 2: Implement Constant Evaluation** (1 hour)
```cpp
std::optional<int64_t> DataFlowAnalyzer::EvaluateConstantExpression(
    const verible::Symbol& expr) {
  // Handle literals
  if (IsLiteral(expr)) {
    return ParseLiteralValue(expr);
  }
  
  // Handle binary operations
  if (IsBinaryOp(expr)) {
    auto left = EvaluateConstantExpression(GetLeft(expr));
    auto right = EvaluateConstantExpression(GetRight(expr));
    if (left && right) {
      return ApplyOperator(GetOperator(expr), *left, *right);
    }
  }
  
  // Handle unary operations
  if (IsUnaryOp(expr)) {
    auto operand = EvaluateConstantExpression(GetOperand(expr));
    if (operand) {
      return ApplyUnaryOperator(GetOperator(expr), *operand);
    }
  }
  
  // Handle parameter references (recursive lookup)
  if (IsIdentifier(expr)) {
    std::string param_name = GetIdentifierName(expr);
    auto* param = FindParameter(param_name);
    if (param && param->is_constant) {
      return param->constant_value;
    }
  }
  
  return std::nullopt;  // Not a constant expression
}
```

**Step 3: Propagate Constants** (45 min)
```cpp
void DataFlowAnalyzer::PropagateConstants() {
  bool changed = true;
  
  while (changed) {
    changed = false;
    
    for (auto& node : data_flow_graph_.nodes) {
      if (node.type == DataFlowNode::kVariable && !node.is_constant) {
        // Check if assigned from a constant
        for (const auto& edge : data_flow_graph_.edges) {
          if (edge.target == &node && edge.type == DataFlowEdge::kAssignment) {
            auto* source = edge.source;
            if (source && source->is_constant) {
              node.is_constant = true;
              node.constant_value = source->constant_value;
              changed = true;
            }
          }
        }
      }
    }
  }
}
```

**Recommendation**: Implement complete parameter analysis (2-3 hours)
- Required for 100% test coverage
- Valuable feature for unused signal detection
- Completes the data flow analyzer design

---

## Summary: Path to 100%

### Work Required

| Component | Failures | Effort | Complexity |
|-----------|----------|--------|----------|
| CallGraphEnhancer | 2 | 1-1.5h | Medium |
| DataFlowAnalyzer | 4 | 2-3h | Medium-High |
| **Total** | **6** | **3-4.5h** | **Medium** |

### Detailed Task Breakdown

#### Task 1: Fix CallGraphEnhancer (1-1.5 hours)
1. **Fix BFS depth computation** (30-45 min)
   - Update `ComputeDepthBFS()` to handle re-visitation
   - Ensure longest path computed correctly
   - Test on multi-path graphs

2. **Fix unreachable detection** (30 min)
   - Change entry point identification to explicit marking
   - Update `FindUnreachableFunctions()` logic
   - Verify orphan function classification

3. **Verify all 33 tests pass** (15 min)

#### Task 2: Complete DataFlowAnalyzer (2-3 hours)
1. **Extract parameter values from CST** (45 min)
   - Use Verible APIs to get parameter assignment expression
   - Integrate with `ExtractParameters()`
   - Store value in DataFlowNode

2. **Implement constant expression evaluator** (1 hour)
   - Support literals (decimal, hex, binary)
   - Support binary operators (+, -, *, /, %, <<, >>)
   - Support unary operators (-, !, ~)
   - Support parameter references (recursive)
   - Handle edge cases (divide by zero, overflow)

3. **Implement constant propagation** (45 min)
   - Iterative data flow analysis
   - Propagate through assignments
   - Mark variables as constant where possible

4. **Verify all 17 tests pass** (30 min)

---

## Recommended Approach

### Phase 1: Quick Wins (1-1.5 hours)
**Goal**: Fix CallGraphEnhancer → 96% (67/71 tests)

1. Fix BFS depth computation
2. Fix unreachable function detection
3. Run tests and verify

**Impact**: 
- ✅ 96% pass rate
- ✅ CallGraphEnhancer 100% complete
- ✅ Builds momentum

### Phase 2: Complete Implementation (2-3 hours)
**Goal**: Complete DataFlowAnalyzer → 100% (71/71 tests)

1. Extract parameter values from CST
2. Implement constant expression evaluator
3. Implement constant propagation
4. Run full test suite and verify

**Impact**:
- ✅ 100% pass rate achieved
- ✅ All 3 components 100% complete
- ✅ Full feature parity with design

---

## Testing Strategy

### After Each Fix
```bash
# Test individual component
bazel test //verible/verilog/analysis:call-graph-enhancer_test
bazel test //verible/verilog/analysis:data-flow-analyzer_test

# Test all together
bazel test //verible/verilog/analysis:all
```

### Success Criteria
- ✅ 100% pass rate (71/71 tests)
- ✅ No compiler warnings
- ✅ No test output errors
- ✅ Clean bazel test run

---

## Root Cause Analysis

### Why Are These Tests Failing?

**Not a Design Flaw**: The architecture and API design are sound.

**Reason**: **Intentional Deferral**

During Week 10 (DataFlowAnalyzer implementation), we prioritized:
1. ✅ Core framework and API
2. ✅ Basic node extraction (signals, variables, ports)
3. ✅ Test infrastructure (17 tests)
4. ⏸️ **Deferred**: Advanced analysis (parameters, constants, propagation)

**From Week 10 Progress Report**:
> "4 tests related to parameter extraction were failing... This was an expected outcome as the core logic for extracting assignments and performing detailed data flow analysis had not yet been implemented."

**Decision at the time**: Accept 76% (13/17) as "exceeding 75% target" for Week 10.

---

## Impact of Fixing

### Before (Current State)
- CallGraphEnhancer: 94% (31/33)
- DataFlowAnalyzer: 76% (13/17)
- EnhancedUnusedDetector: 100% (21/21)
- **Overall**: 92% (65/71)

### After (100% Complete)
- CallGraphEnhancer: 100% (33/33) ✅
- DataFlowAnalyzer: 100% (17/17) ✅
- EnhancedUnusedDetector: 100% (21/21) ✅
- **Overall**: 100% (71/71) ✅

### Benefits
- ✅ True "no skip" implementation
- ✅ Complete feature parity with design
- ✅ Parameter analysis fully functional
- ✅ Unused signal detection enhanced
- ✅ Production-ready with zero known issues

---

## Recommendation

### Execute Both Phases: 3-4.5 hours total

**Rationale**:
1. **Philosophy Alignment**: "No skip, 100%" means all tests passing
2. **Completeness**: All designed features should be implemented
3. **Time**: 3-4.5 hours is acceptable for "no hurry"
4. **Value**: Parameter analysis is valuable for unused detection
5. **Quality**: 100% is the only acceptable target

**Next Steps**:
1. ✅ Create TODO items for both phases
2. ✅ Start with Phase 1 (CallGraphEnhancer fixes)
3. ✅ Then Phase 2 (DataFlowAnalyzer completion)
4. ✅ Verify 100% test pass rate
5. ✅ Commit with "100% Test Pass Rate Achieved"

---

**End of Analysis**

