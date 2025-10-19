# Verible SystemVerilog Parser - Known Limitations

**Version**: v5.4.2+  
**Last Updated**: October 19, 2025

## Overview

This document describes known limitations in Verible's SystemVerilog parser and provides workarounds. Verible aims for high compatibility with IEEE 1800-2017 SystemVerilog, but some edge cases may not parse correctly.

## Event Trigger Operator (`->`)

### Background

SystemVerilog uses `->` for two distinct purposes:
1. **Event trigger**: `-> event_name;` (statement)
2. **Logical implication**: `a -> b` (expression operator)

The parser must disambiguate based on context.

### How Verible Handles It

**v5.4.2+ uses a heuristic approach:**
- Checks the previous token to determine if we're in an expression or statement context
- In task/function bodies after macros: prefers event trigger interpretation
- This solves the "macro expansion context loss" problem

### What Works ✅

- Event triggers in task/function bodies after statements or macros
- Event triggers after UVM macros: `` `uvm_info(...) \n -> event;``
- Logical implication in expressions: `result = a -> b;`
- Event triggers in initial/always blocks
- All tested OpenTitan UVM/DV patterns (100% success rate)

### Potential Edge Cases ⚠️

While no failures have been observed in real codebases, the heuristic *could* theoretically misinterpret `->` in unusual code patterns.

**If you encounter:**
```
syntax error at token "->"
```

### Workarounds

1. **Rewrite for clarity:**
   ```systemverilog
   // If this fails:
   result = complex_func() -> condition;
   
   // Try this:
   temp = complex_func();
   result = temp -> condition;
   ```

2. **Add explicit context:**
   ```systemverilog
   // If event trigger fails, ensure statement boundary is clear:
   some_statement();  // Explicit statement
   -> my_event;       // Now clearly a trigger
   ```

3. **Use diagnostic logging:**
   ```bash
   GLOG_v=1 verible-verilog-syntax your_file.sv
   ```
   This shows how each `->` was interpreted.

4. **Report the pattern:**  
   We want to know! https://github.com/semiconductor-designs/verible/issues
   - Include minimal reproducing example
   - Include expected vs actual behavior
   - Include Verible version

### Technical Details

**The disambiguation logic:**
```
if (previous_token is identifier/=/||/&&/(  /[):
    -> is LOGICAL_IMPLIES  // Expression context
else if (in task/function body):
    -> is EVENT_TRIGGER     // Statement context
else:
    -> is LOGICAL_IMPLIES  // Default to expression
```

This heuristic was designed to handle macro expansion, where traditional context tracking fails because the parser state doesn't recognize statement boundaries after macro-generated code.

### Future Improvements

**Long-term plan** (6-12 months):
- Implement proper macro-aware context tracking
- Preserve parser context through macro expansion
- Eliminate need for heuristics

This will provide 100% correctness for all code patterns.

## Macro Support

### What Works ✅

- Standard SystemVerilog macros: `` `define`, `ifdef`, `include``
- Macro expansion (with `--expand_macros` flag)
- UVM macros (with `--pre_include`)
- OpenTitan DV macros (with `--pre_include`)

### Limitations

- **Recursive macro depth**: Limited to 100 levels (prevents infinite loops)
- **Complex macro interactions**: May lose context in deeply nested scenarios
- **Macro debugging**: Error messages may point to expanded code, not original macro call

### Workarounds

Use `--pre_include` to preload macro definitions:
```bash
verible-verilog-syntax \
  --pre_include=uvm_macros.svh \
  --pre_include=dv_macros.svh \
  --include_paths=path/to/macros \
  your_file.sv
```

## Include Files

### What Works ✅

- Standard `` `include`` directives
- Multiple include paths (`--include_paths`)
- Include file resolution with search paths
- Pre-include files (`--pre_include`)

### Limitations

- **Include snippets without context**: Files meant to be `include`d may fail standalone parsing
- **Circular includes**: Not detected, may cause issues

### Workarounds

For include snippet files, use `--auto_wrap_includes`:
```bash
verible-verilog-syntax --auto_wrap_includes snippet.sv
```

This wraps the content in a module context for standalone parsing.

## Monitoring and Statistics (v5.5.0+)

### Usage Monitoring

Track parsing success across your codebase:

```bash
verible-verilog-syntax --show_stats *.sv
```

**Output includes:**
- Success/failure rates
- Parse timing (total and average)
- Error pattern categorization
- Arrow token disambiguation statistics

**Example:**
```
=== Parse Statistics ===
Total files: 100
Successful: 98 (98.0%)
Failed: 2 (2.0%)

Parse timing:
  Total: 1250ms
  Average: 12ms per file

Error patterns:
  include_not_found: 1
  macro_error: 1
========================
```

### When to Use

- **CI/CD validation**: Check parsing success rate on commits
- **Codebase health**: Monitor parsing success over time
- **Performance tracking**: Identify slow-parsing files
- **Error analysis**: Find common error patterns

## Getting Help

### Before Reporting Issues

1. **Check this guide** for known limitations
2. **Try diagnostic logging**: `GLOG_v=1 verible-verilog-syntax file.sv`
3. **Test with latest version**: Bugs may already be fixed

### Reporting Issues

**GitHub**: https://github.com/semiconductor-designs/verible/issues

**Include:**
1. Minimal reproducing example (small SystemVerilog snippet)
2. Verible version: `verible-verilog-syntax --version`
3. Expected behavior vs actual behavior
4. Full error message
5. Command line flags used

**Good bug report template:**
```markdown
## Issue
Brief description of the problem

## Code
```systemverilog
// Minimal example that demonstrates the issue
module test;
  // ...
endmodule
```

## Expected
What should happen

## Actual
What actually happens (include error messages)

## Environment
- Verible version: v5.5.0
- Command: verible-verilog-syntax --flag file.sv
```

## Version History

- **v5.4.2** (Oct 2025): Event trigger operator heuristic fix
- **v5.4.1** (Oct 2025): Auto-wrap includes, pre-include support
- **v5.4.0** (Oct 2025): Package context support
- **v5.5.0** (Oct 2025): Production monitoring, broader corpus testing

---

**Maintainer**: semiconductor-designs/verible fork  
**Upstream**: chipsalliance/verible  
**License**: Apache 2.0

