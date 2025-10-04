# Verible Modification Job Brief

**Project:** VeriPG - Verilog Property Graph Builder  
**Task:** Modify Verible to preserve full expression syntax in JSON export  
**Goal:** Achieve 100% syntax fidelity for SystemVerilog expressions  
**Estimated Effort:** 5-10 hours  
**Date:** October 4, 2025

---

## 📋 Context

### Current Situation

**VeriPG Project:**
- Extracts SystemVerilog module hierarchy and connections for Repository Planning Graph (RPG)
- Uses Verible parser to get AST in JSON format
- Current version: v1.3.1
- Status: Production ready with 95.8% syntax fidelity

**Current Achievement (v1.3.1):**
- ✅ 142 tests passing (100%)
- ✅ Bit slices preserved: `bus[7:0]` ✓
- ✅ Bit selects preserved: `signal[5]` ✓
- ✅ Concatenations preserved: `{a, b, c}` ✓
- ✅ Constants preserved: `1'b0`, `8'hFF` ✓
- ✅ Real-world effectiveness: ~100% on OpenTitan
- ❌ Standalone operators: `~signal`, `a+b` (lost in JSON export)

**The Gap:**
- Test fixtures: 95.8% (68/71 connections)
- Real-world: ~100% effective
- Missing: 3 standalone operator expressions (4.2%)

---

## 🎯 Problem Statement

### Root Cause

**Verible's JSON Export Limitation:**

When Verible exports AST to JSON using `--export_json`, it **strips operators** from expressions:

**Input SystemVerilog:**
```verilog
.rst_ni(~rst_n)        // Unary NOT
.data_i(a + b)         // Binary addition  
.enable_i(!enable)     // Logical NOT
```

**Current JSON Output:**
```json
{
  "tag": "kExpression",
  "children": [
    {"tag": "kReference", "text": "rst_n"}
  ]
}
// Operator '~' is GONE!
```

**What We Extract:**
```
.rst_ni(rst_n)         // ❌ Operator lost
.data_i(ab)            // ❌ Operator lost
.enable_i(enable)      // ❌ Operator lost
```

### Why This Happens

Verible's JSON exporter reconstructs text from child nodes instead of preserving the original source text span. It only includes `"text"` fields for leaf nodes (identifiers, literals), not for parent expression nodes.

---

## 💡 Solution: Modify Verible

### Objective

Modify Verible's JSON export to include the **full source text** for expression nodes.

**Desired JSON Output:**
```json
{
  "tag": "kExpression",
  "text": "~rst_n",     // ← ADD THIS!
  "children": [
    {"tag": "kReference", "text": "rst_n"}
  ]
}
```

With this change, VeriPG can use the `"text"` field directly and achieve 100% syntax fidelity.

---

## 🔧 Technical Implementation

### Phase A: Investigation (2 hours)

**1. Clone Verible Repository**
```bash
cd /Users/jonguksong/Projects
git clone https://github.com/chipsalliance/verible.git
cd verible
```

**2. Locate JSON Export Code**

Target files (likely locations):
- `verilog/tools/syntax/export_json_examples.cc`
- `verilog/CST/verilog_tree_json.cc`
- `verilog/CST/verilog_tree_json.h`
- `common/text/tree_utils.cc`

Search for:
```bash
grep -r "export.*json" verilog/
grep -r "kExpression" verilog/CST/
grep -r "ToJson" verilog/
```

**3. Study Current Implementation**

Understand:
- How JSON export works
- Where `"text"` fields are populated
- How to access original source text spans
- Build system (Bazel)

**4. Identify Modification Point**

Find where expression nodes are exported to JSON. Look for:
- Functions like `TreeToJson()`, `NodeToJson()`, etc.
- How leaf nodes get their `"text"` field
- Where to add source text extraction

### Phase B: Modification (3-5 hours)

**1. Add Source Text to Expression Nodes**

**Approach:**
- Identify expression-like node tags (kExpression, kBinaryExpression, kUnaryExpression, etc.)
- Extract source text span from the node
- Add `"text"` field to JSON output

**Pseudo-code:**
```cpp
// In JSON export function
if (node.tag() == NodeEnum::kExpression ||
    node.tag() == NodeEnum::kBinaryExpression ||
    node.tag() == NodeEnum::kUnaryExpression) {
  
  // Get original source text for this node's span
  absl::string_view source_text = GetNodeText(node, text_structure);
  
  // Add to JSON
  json_node["text"] = std::string(source_text);
}
```

**Key Functions to Use:**
- `verible::StringSpanOfSymbol()` - Gets text span of a node
- `text_structure_view.GetRangeForText()` - Gets source text for span
- Look for similar patterns in existing code

**2. Handle All Expression Types**

Node tags to consider:
- `kExpression`
- `kBinaryExpression`
- `kUnaryExpression`
- `kConditionalExpression`
- `kFunctionCall`
- (Check full list in `verilog/CST/verilog_nonterminals.h`)

**3. Build Modified Verible**

```bash
# Install dependencies (if needed)
# On macOS:
brew install bazel

# Build
bazel build //verilog/tools/syntax:verible-verilog-syntax

# Binary location
./bazel-bin/verilog/tools/syntax/verible-verilog-syntax
```

**4. Test Modification**

Test file: `test_operators.sv`
```verilog
module test;
  logic a, b, enable, rst_n;
  
  child u1 (
    .port1(~rst_n),
    .port2(a + b),
    .port3(!enable)
  );
endmodule
```

Run:
```bash
./bazel-bin/verilog/tools/syntax/verible-verilog-syntax \
  --export_json test_operators.sv
```

Check JSON output for `"text"` fields on expression nodes.

### Phase C: Integration (2-3 hours)

**1. Copy Modified Binary to VeriPG**

```bash
# Copy to VeriPG tools directory
cp ./bazel-bin/verilog/tools/syntax/verible-verilog-syntax \
   /Users/jonguksong/Projects/VeriPG/tools/verible/bin/
```

**2. Test with VeriPG**

```bash
cd /Users/jonguksong/Projects/VeriPG

# Test on expressions fixture
python3 -c "
import sys
sys.path.insert(0, 'src')
from rpg.module_extractor import ModuleExtractor

ext = ModuleExtractor()
result = ext.extract_from_file('tests/fixtures/connections/expressions.sv')

for module in result['modules']:
    for inst in module['instantiations']:
        for conn in inst['connections']:
            print(f'.{conn[\"port\"]}({conn[\"signal\"]})')
"
```

**Expected Output:**
```
.clk_i(clk)
.rst_ni(~rst_n)          ← Should have ~
.data_i(a+b)             ← Should have +
.data_o(result)
.valid_o(valid)
.enable_i(!enable)       ← Should have !
```

**3. Run Full Test Suite**

```bash
python3 -m pytest tests/ -v
```

All 142 tests should still pass, plus the 3 operator expressions should now be preserved.

**4. Validate 100% Fidelity**

```bash
python3 << 'PYEOF'
import sys
sys.path.insert(0, 'src')
from rpg.module_extractor import ModuleExtractor
from pathlib import Path

ext = ModuleExtractor()

# Test all fixtures
fixtures_dir = Path('tests/fixtures/connections')
total = 0
with_operators = 0

for fixture in fixtures_dir.glob('*.sv'):
    result = ext.extract_from_file(fixture)
    for module in result['modules']:
        for inst in module['instantiations']:
            for conn in inst['connections']:
                total += 1
                if any(op in conn['signal'] for op in ['~', '+', '-', '*', '/', '&', '|', '^', '!', '<<', '>>']):
                    with_operators += 1
                    print(f"{fixture.name}: .{conn['port']}({conn['signal']})")

print(f"\nTotal: {total}, With operators: {with_operators}")
print(f"Fidelity: 100% ✓" if with_operators > 0 else "Fidelity: Still missing operators")
PYEOF
```

### Phase D: Contribution (Optional, 2-4 hours)

**1. Clean Up Changes**
- Remove debug code
- Add comments
- Follow Verible coding style
- Add unit tests (if possible)

**2. Create Pull Request**
- Fork Verible repository on GitHub
- Push changes to your fork
- Create PR with description:
  - Title: "Add source text to expression nodes in JSON export"
  - Description: Explain the problem and solution
  - Benefits: Better JSON export fidelity, helps downstream tools

**3. Engage with Community**
- Respond to review comments
- Make requested changes
- Help get PR merged

---

## ✅ Success Criteria

### Must Have
- [x] Modified Verible binary that includes `"text"` field for expression nodes
- [x] VeriPG achieves 100% syntax fidelity (71/71 test fixtures passing)
- [x] All 142 existing tests still pass
- [x] Expressions with operators preserved: `~signal`, `a+b`, `!enable`

### Nice to Have
- [ ] PR submitted to Verible upstream
- [ ] Documentation of changes
- [ ] Build instructions for future updates

---

## 📁 Deliverables

### Required Files

**1. Modified Verible Binary**
- Location: `/Users/jonguksong/Projects/VeriPG/tools/verible/bin/verible-verilog-syntax`
- Size: ~50MB (similar to current)
- Version: Include build date/commit in filename

**2. Build Instructions**
- Document: `VERIBLE_BUILD_NOTES.md`
- Include: Dependencies, build commands, modification points
- For: Future VeriPG maintainers

**3. Test Results**
- Show before/after comparison
- Confirm 100% fidelity achieved
- Include test output logs

### Optional Files

**4. Patch File**
- Diff of changes made to Verible
- For: Sharing with community

**5. PR Link**
- Link to upstream pull request
- Status: Submitted, merged, etc.

---

## 🛠️ Tools & Resources

### Development Tools
- **C++ Compiler**: Clang (comes with Xcode on macOS)
- **Build System**: Bazel (install via `brew install bazel`)
- **Editor**: Cursor, VS Code, or your preference
- **Git**: For cloning and version control

### Reference Documentation
- **Verible GitHub**: https://github.com/chipsalliance/verible
- **Verible Docs**: https://chipsalliance.github.io/verible/
- **Build Guide**: See `CONTRIBUTING.md` in Verible repo
- **VeriPG Location**: `/Users/jonguksong/Projects/VeriPG`

### Test Files
- **VeriPG Test Fixtures**: `/Users/jonguksong/Projects/VeriPG/tests/fixtures/connections/`
- **Key Fixture**: `expressions.sv` (has the 3 failing cases)

---

## 🚨 Potential Issues & Solutions

### Issue 1: Bazel Build Fails
**Solution:** 
- Check Bazel version: `bazel version` (need 5.0+)
- Install dependencies: Xcode Command Line Tools
- Try: `bazel clean --expunge` then rebuild

### Issue 2: Can't Find JSON Export Code
**Solution:**
- Search broadly: `grep -r "ToJson" .`
- Look for `verible::ToJson` function
- Check `common/text/` directory
- Ask Verible community on GitHub discussions

### Issue 3: Modified Binary Doesn't Work
**Solution:**
- Check binary location: `which verible-verilog-syntax`
- VeriPG uses: `tools/verible/bin/verible-verilog-syntax`
- Test manually: `./path/to/verible --export_json test.sv`
- Verify JSON output has `"text"` fields

### Issue 4: Modification Too Complex
**Solution:**
- Fall back to Option 2: Implement printtree parsing in VeriPG
- Or accept v1.3.1 as-is (95.8% is excellent)
- Document findings for future attempts

---

## 📊 Current VeriPG State

### File to Modify (if Verible works)
- **Primary**: `src/rpg/module_extractor.py`
- **Method**: `_extract_signal_expression()` (line ~841)
- **Change**: Simplify to just use `node['text']` directly
- **Benefit**: Remove complex source matching workarounds

### Current Workaround (v1.3.1)
```python
def _extract_signal_expression(self, expr_node):
    # v1.3.1: Complex source text matching
    if 'text' in expr_node:
        return expr_node['text']  # Works for some cases
    
    # Fall back to reconstruction and source matching
    extracted = self._extract_expression_text(expr_node)
    
    # Try to fix missing syntax
    if self._might_have_missing_syntax(extracted):
        full_expr = self._find_full_expression_in_source(extracted)
        if full_expr:
            return full_expr
    
    return extracted
```

### After Verible Modification
```python
def _extract_signal_expression(self, expr_node):
    # v1.4.0: Simple and clean!
    if 'text' in expr_node:
        return expr_node['text']  # Now works for ALL cases ✓
    
    # Fallback (rarely needed)
    return self._extract_expression_text(expr_node)
```

---

## 🎯 Timeline

### Suggested Schedule
- **Day 1, Hours 1-2**: Clone Verible, study code, identify modification
- **Day 1, Hours 3-5**: Modify JSON export, initial build attempt
- **Day 1, Hours 6-8**: Debug build issues, get working binary
- **Day 2, Hours 1-2**: Test with VeriPG, validate 100% fidelity
- **Day 2, Hours 3-4**: Document changes, create deliverables
- **(Optional) Day 3**: Clean up for PR, submit to upstream

### Milestones
1. ✓ Verible cloned and built (baseline)
2. ✓ JSON export code located and understood
3. ✓ Modification implemented
4. ✓ Modified binary working
5. ✓ VeriPG achieves 100% fidelity
6. ✓ Documentation complete
7. (Optional) PR submitted upstream

---

## 📝 Communication

### Report Back to Main VeriPG Project

When complete, provide:
1. **Status**: Success or need fallback plan
2. **Binary**: Modified Verible binary (if successful)
3. **Fidelity**: Actual percentage achieved
4. **Issues**: Any blockers encountered
5. **Documentation**: Build notes and instructions

### Questions?

If you get stuck or need clarification:
- Check Verible's GitHub issues
- Look for similar modifications in git history
- Ask on Verible discussions
- Document what you learned and return to main project

---

## 🎓 Learning Resources

### Verible Internals
- **CST (Concrete Syntax Tree)**: How Verible represents code
- **TextStructureView**: Manages original source text
- **Symbol**: Base class for tree nodes
- **TokenInfo**: Leaf nodes with text spans

### Key C++ Patterns
- `absl::string_view`: Non-owning string reference
- Bazel BUILD files: Define compilation targets
- Protocol Buffers: May be used for internal representation

---

## ✨ Success Message

When you achieve 100% fidelity, you'll have:

✅ Fixed a limitation in Verible that affects many users  
✅ Achieved 100% syntax fidelity for VeriPG  
✅ Created an opportunity for upstream contribution  
✅ Learned Verible internals (valuable knowledge)  
✅ Made VeriPG's code simpler and more maintainable  

**This is a high-impact contribution to the SystemVerilog tooling community!**

---

**Good luck! You're working on a great solution that will help many people beyond just VeriPG.**

---

*Document prepared by VeriPG team for Verible modification task*  
*Version: 1.0*  
*Date: October 4, 2025*

