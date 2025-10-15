# CallGraph Deep Dive - Investigation & Fix Plan

**Mission**: Fix CallGraph edge detection (0 edges → accurate edges)

---

## 🔍 ROOT CAUSE ANALYSIS

### The Problem
**CallGraph has nodes but ZERO edges!**
- Test: 2 functions defined → 2 nodes ✅
- Test: 1 function calls another → **0 edges** ❌

### Why?
Looking at `call-graph.cc:40-67` (`BuildFromNode`):

```cpp
void CallGraph::BuildFromNode(const SymbolTableNode& node) {
  // If this is a function or task, add it as a node
  if (info.metatype == SymbolMetaType::kFunction ||
      info.metatype == SymbolMetaType::kTask) {
    AddNode(func_name);
    
    // Extract calls from this function/task's definition
    // Look through local_references_to_bind for call sites
    for (const auto& ref : info.local_references_to_bind) {  // ← LINE 54
      ExtractCallsFromReferenceTree(func_name, *ref.components);
    }
  }
  
  // Recursively traverse children
  for (const auto& child : node) {
    BuildFromNode(child.second);
  }
}
```

**THE ISSUE**: Line 54 only looks at `local_references_to_bind` **within function/task definitions**.

**What about calls from `initial` blocks?**
- `initial` is NOT a function/task
- So the code at line 44-61 **never executes** for `initial` blocks
- **Calls from `initial` are never extracted!**

### Test Case Breakdown

```systemverilog
module test;
  initial begin
    used_function();  // ← Call from 'initial' block
  end
  
  function automatic void used_function();
    // This is called
  endfunction
  
  function automatic void unused_function();
    // This is NEVER called
  endfunction
endmodule
```

**What CallGraph sees:**
1. Traverses module (not function/task, skip line 44-61)
2. Encounters `initial` (not function/task, skip line 44-61)
3. Encounters `used_function` (IS function, add node) ✅
4. Encounters `unused_function` (IS function, add node) ✅
5. **NEVER extracts the call from `initial`!** ❌

**Result**: 2 nodes, 0 edges

---

## 🎯 THE FIX

### Strategy
**Expand edge extraction beyond just function/task bodies!**

We need to extract calls from:
1. ✅ Function/task definitions (current)
2. ❌ Initial blocks (MISSING!)
3. ❌ Always blocks (MISSING!)
4. ❌ Module-level procedural code (MISSING!)

### Implementation Plan

#### Step 1: Extract Calls from ALL Nodes (TDD)
**Current**:
```cpp
if (info.metatype == SymbolMetaType::kFunction ||
    info.metatype == SymbolMetaType::kTask) {
  AddNode(func_name);
  ExtractCalls(...);  // Only here!
}
```

**Fixed**:
```cpp
// FIRST: If this is a function/task, add it as a node
if (info.metatype == SymbolMetaType::kFunction ||
    info.metatype == SymbolMetaType::kTask) {
  AddNode(func_name);
}

// THEN: Extract calls from ANY node that has references
// This covers initial, always, and procedural code
ExtractCallsFromNode(node);
```

#### Step 2: New Helper Function
```cpp
void CallGraph::ExtractCallsFromNode(const SymbolTableNode& node) {
  const auto& info = node.Value();
  
  // Determine the "caller" context
  // - If we're in a function/task, that's the caller
  // - If we're in module/initial/always, use special name like "$initial"
  std::string caller_context = DetermineCallerContext(node);
  
  // Extract calls from local_references_to_bind
  for (const auto& ref : info.local_references_to_bind) {
    if (!ref.Empty() && ref.components) {
      ExtractCallsFromReferenceTree(caller_context, *ref.components);
    }
  }
  
  // Recursively extract from children
  for (const auto& child : node) {
    ExtractCallsFromNode(child.second);
  }
}
```

#### Step 3: Determine Caller Context
```cpp
std::string CallGraph::DetermineCallerContext(const SymbolTableNode& node) {
  const auto& info = node.Value();
  const auto* key = node.Key();
  
  // If function/task, use its name
  if ((info.metatype == SymbolMetaType::kFunction ||
       info.metatype == SymbolMetaType::kTask) && 
      key && !key->empty()) {
    return std::string(*key);
  }
  
  // For procedural blocks, use special names
  // This helps track what's called from module-level code
  // (Note: These won't be marked as dead since they're entry points)
  return "$module_scope";
}
```

---

## 📋 TDD IMPLEMENTATION PLAN

### Phase 1: Write Failing Test (30 mins)
**File**: `verible/verilog/analysis/call-graph_test.cc`

Add test:
```cpp
TEST(CallGraphTest, ExtractCallsFromInitialBlock) {
  // Test code with initial block calling a function
  std::string code = R"(
module test;
  initial begin
    my_func();
  end
  
  function void my_func();
  endfunction
endmodule
)";
  
  // Parse, build symbol table, build call graph
  // ...
  
  // EXPECT: 1 node (my_func) + 1 edge ($module_scope -> my_func)
  EXPECT_EQ(call_graph.GetNodeCount(), 1);
  EXPECT_GE(call_graph.GetEdgeCount(), 1);  // At least 1 edge!
}
```

**Run**: Should FAIL (currently 0 edges)

### Phase 2: Implement Fix (1-2 hours)

**File**: `verible/verilog/analysis/call-graph.h`
- Add `ExtractCallsFromNode` helper
- Add `DetermineCallerContext` helper

**File**: `verible/verilog/analysis/call-graph.cc`
- Implement new helpers
- Refactor `BuildFromNode` to call `ExtractCallsFromNode`

### Phase 3: Verify Fix (30 mins)
- Run new test → should PASS
- Run all existing tests → should still PASS
- Run integration tests → should now find dead code!

### Phase 4: Update Integration Tests (30 mins)
**File**: `dead-code-eliminator_integration_test.cc`
- Remove "DOCUMENTED BEHAVIOR" comments
- Update expectations to actually detect dead code:
```cpp
// Was: EXPECT_EQ(report.total_dead_count, 0) << "No edges limitation";
// Now: EXPECT_EQ(report.total_dead_count, 1) << "Should find unused_function";
```

---

## ⚠️ POTENTIAL ISSUES

### Issue 1: Module-level calls create "fake" nodes
**Problem**: `$module_scope` isn't a real function
**Solution**: Filter these out in `FindDeadCode()` logic

### Issue 2: Always blocks need similar treatment
**Problem**: Calls from `always @(posedge clk)` also missed
**Solution**: Same fix handles all procedural blocks

### Issue 3: Performance with large codebases
**Problem**: Extracting calls from ALL nodes (not just functions)
**Solution**: Still only traverse once, just look in more places

---

## ✅ SUCCESS CRITERIA

### Must Have
1. ✅ Extract calls from `initial` blocks
2. ✅ Extract calls from `always` blocks
3. ✅ New test passes
4. ✅ All existing tests pass
5. ✅ Integration test finds dead code

### Nice to Have
1. ✅ Extract calls from module-level code
2. ✅ Handle hierarchical calls (a.b.c())
3. ✅ Performance acceptable

---

## 📊 EXPECTED IMPACT

### Before Fix
```
Test code: initial begin used_function(); end
Result: nodes=2, edges=0, dead_count=0
Issue: Can't detect dead code
```

### After Fix
```
Test code: initial begin used_function(); end
Result: nodes=2, edges=1, dead_count=1
Success: Detects unused_function as dead! ✅
```

---

## 🎯 BOTTOM LINE

**Root Cause**: CallGraph only extracts calls from function/task bodies.
**Fix**: Extract calls from ALL nodes (initial, always, module-level).
**Effort**: 2-3 hours (TDD approach).
**Impact**: CallGraph becomes truly useful! 🚀

**Let's do it!** No hurry. TDD. Perfection! 🎯

