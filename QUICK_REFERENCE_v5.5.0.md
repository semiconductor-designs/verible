# Verible v5.5.0 Quick Reference

**Fast answers for common tasks**

## For OpenTitan Users

### Parse DV/UVM Files
```bash
verible-verilog-syntax \
  --pre_include=hw/dv/sv/dv_utils/dv_macros.svh \
  --include_paths=third_party/uvm/src,hw/dv/sv/dv_utils \
  your_dv_file.sv
```

### Parse Include Snippet Files
```bash
verible-verilog-syntax --auto_wrap_includes your_snippet.sv
```

### Parse with Package Context
```bash
verible-verilog-syntax \
  --package_context=my_pkg.sv \
  --include_paths=path/to/includes \
  your_file.sv
```

## Monitoring and Statistics

### Track Parsing Success
```bash
verible-verilog-syntax --show_stats *.sv
```

### Batch Processing with Stats
```bash
find hw/ -name "*.sv" | xargs verible-verilog-syntax --show_stats
```

### Enable Diagnostic Logging
```bash
GLOG_v=1 verible-verilog-syntax file.sv
```

## Common Flags

| Flag | Purpose | Example |
|------|---------|---------|
| `--pre_include=<file>` | Preload macro definitions | `--pre_include=uvm_macros.svh` |
| `--include_paths=<paths>` | Set include search paths | `--include_paths=inc1,inc2` |
| `--package_context=<file>` | Load package context | `--package_context=pkg.sv` |
| `--auto_wrap_includes` | Wrap snippets in module | `--auto_wrap_includes` |
| `--show_stats` | Show parse statistics | `--show_stats` |
| `--expand_macros` | Expand macros (default: false) | `--expand_macros=true` |
| `--preprocess` | Enable preprocessing | `--preprocess=true` |

## Known Issues (v5.5.0)

### Fixed ✅
- Event trigger operator (`->`) after macros
- Include snippet parsing
- Package context macro loading
- Macro expansion context loss

### Limitations ⚠️
- Heuristic-based `->` disambiguation (works for all tested cases)
- Macro recursion depth limited to 100
- Include snippets need `--auto_wrap_includes`

## Error Messages

### "syntax error at token '->'"
**Cause**: Event trigger operator ambiguity  
**Fix**: Use diagnostic logging to see disambiguation:
```bash
GLOG_v=1 verible-verilog-syntax file.sv
```
**Report if**: Pattern is valid SystemVerilog but still fails

### "Include file not found"
**Cause**: Missing include path  
**Fix**: Add path with `--include_paths`:
```bash
verible-verilog-syntax --include_paths=path/to/includes file.sv
```

### "macro not defined"
**Cause**: Macro used but not defined  
**Fix**: Use `--pre_include` to load macro definitions:
```bash
verible-verilog-syntax --pre_include=macros.svh file.sv
```

## Testing Your Codebase

### Quick Validation
```bash
# Test all files, show summary
find . -name "*.sv" -exec verible-verilog-syntax {} \; 2>&1 | \
  grep -c "syntax error" || echo "All files passed!"
```

### Detailed Validation
```bash
# Run with stats
verible-verilog-syntax --show_stats $(find . -name "*.sv")
```

### CI/CD Integration
```bash
#!/bin/bash
# Exit with error if any file fails to parse

FAIL_COUNT=0
for file in $(find . -name "*.sv"); do
  if ! verible-verilog-syntax "$file" &>/dev/null; then
    echo "FAIL: $file"
    ((FAIL_COUNT++))
  fi
done

if [ $FAIL_COUNT -gt 0 ]; then
  echo "❌ $FAIL_COUNT files failed to parse"
  exit 1
else
  echo "✅ All files parsed successfully"
fi
```

## Performance Tips

### Slow Parsing?
1. **Check file size**: Files >10K lines may be slow
2. **Disable macro expansion**: Use `--expand_macros=false` (default)
3. **Limit includes**: Only add necessary include paths
4. **Use statistics**: `--show_stats` identifies slow files

### Batch Processing
```bash
# Parallel processing (GNU parallel)
find . -name "*.sv" | parallel verible-verilog-syntax {}

# With stats aggregation
find . -name "*.sv" | xargs verible-verilog-syntax --show_stats
```

## Corpus Testing (v5.5.0+)

### Setup Test Corpus
```bash
./scripts/setup_test_corpus.sh
```

### Run Broader Tests
```bash
./scripts/test_broader_corpus.sh
```

### Analyze Failures
```bash
./scripts/analyze_corpus_failures.sh
```

## Support and Resources

### Documentation
- **Internal OpenTitan Users**: [OPENTITAN_USAGE_GUIDE.md](OPENTITAN_USAGE_GUIDE.md)
- **External Users**: [docs/USER_GUIDE_LIMITATIONS.md](docs/USER_GUIDE_LIMITATIONS.md)
- **This Repository**: https://github.com/semiconductor-designs/verible
- **Upstream**: https://github.com/chipsalliance/verible

### Reporting Issues
- **This Fork**: https://github.com/semiconductor-designs/verible/issues
- **Upstream**: https://github.com/chipsalliance/verible/issues

### Getting Help
1. Check documentation first
2. Search existing issues
3. Create new issue with:
   - Minimal reproducing example
   - Verible version
   - Expected vs actual behavior

## Version Information

```bash
# Check version
verible-verilog-syntax --version

# Get help
verible-verilog-syntax --help
```

## Feature Matrix

| Feature | v5.4.0 | v5.4.1 | v5.4.2 | v5.5.0 |
|---------|--------|--------|--------|--------|
| Package context | ✅ | ✅ | ✅ | ✅ |
| Pre-include files | ❌ | ✅ | ✅ | ✅ |
| Auto-wrap includes | ❌ | ✅ | ✅ | ✅ |
| Event trigger fix | ❌ | ❌ | ✅ | ✅ |
| Parse statistics | ❌ | ❌ | ❌ | ✅ |
| Corpus testing | ❌ | ❌ | ❌ | ✅ |

---

**Quick Reference Version**: v5.5.0  
**Last Updated**: October 19, 2025  
**For detailed information**, see full documentation links above.

