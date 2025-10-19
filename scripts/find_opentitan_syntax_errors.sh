#!/bin/bash
# Find OpenTitan files with syntax errors even with proper flags

VERIBLE="./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax"
OPENTITAN="/Users/jonguksong/Projects/OpenTitan-to-RPG/subtrees/opentitan"
PRE_INCLUDE="$OPENTITAN/hw/dv/sv/dv_utils/dv_macros.svh"
INCLUDE_PATHS="third_party/uvm/src,$OPENTITAN/hw/dv/sv/dv_utils"

echo "========================================="
echo "OpenTitan Files with Syntax Errors"
echo "========================================="
echo ""
echo "Testing known problematic files..."
echo ""

# Files known to have parser issues
PROBLEMATIC_FILES=(
  "$OPENTITAN/hw/dv/sv/spi_agent/spi_monitor.sv"
  "$OPENTITAN/hw/dv/sv/cip_lib/cip_base_env_cfg.sv"
  "$OPENTITAN/hw/dv/sv/cip_lib/cip_base_vseq.sv"
  "$OPENTITAN/hw/dv/sv/dv_lib/dv_base_env_cfg.sv"
  "$OPENTITAN/hw/dv/sv/dv_lib/dv_base_reg_map.sv"
)

for file in "${PROBLEMATIC_FILES[@]}"; do
  if [ ! -f "$file" ]; then
    echo "⚠️  File not found: $(basename $file)"
    continue
  fi
  
  filename=$(basename "$file")
  
  # Parse with full DV context
  errors=$($VERIBLE --pre_include="$PRE_INCLUDE" --include_paths="$INCLUDE_PATHS" "$file" 2>&1)
  
  if echo "$errors" | grep -q "Syntax error"; then
    error_count=$(echo "$errors" | grep -c "syntax error at token" || echo "0")
    echo "❌ $filename ($error_count errors)"
    
    # Extract unique error types
    echo "$errors" | grep "syntax error at token" | sed 's/.*syntax error at token "\([^"]*\)".*/  - Error: \1/' | sort -u | head -5
    echo ""
  else
    echo "✅ $filename (no errors)"
  fi
done

echo ""
echo "========================================="
echo "Categorizing Error Types"
echo "========================================="
echo ""

# Categorize by error type
echo "1. Event Trigger Operator (->) Errors:"
grep -l "^.* -> .*;" "$OPENTITAN/hw/dv/sv"/*/*.sv 2>/dev/null | while read f; do
  if $VERIBLE --pre_include="$PRE_INCLUDE" --include_paths="$INCLUDE_PATHS" "$f" 2>&1 | grep -q 'syntax error at token "->"'; then
    echo "   - $(basename $f)"
  fi
done | head -5

echo ""
echo "2. Other Parser Limitations:"
for file in "${PROBLEMATIC_FILES[@]}"; do
  if [ -f "$file" ]; then
    errors=$($VERIBLE --pre_include="$PRE_INCLUDE" --include_paths="$INCLUDE_PATHS" "$file" 2>&1 | grep "syntax error at token" | grep -v '"->"')
    if [ -n "$errors" ]; then
      echo "   - $(basename $file):"
      echo "$errors" | sed 's/.*syntax error at token "\([^"]*\)".*/     Token: \1/' | sort -u | head -3
    fi
  fi
done

