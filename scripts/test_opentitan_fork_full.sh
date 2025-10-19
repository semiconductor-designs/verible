#!/bin/bash
# Full OpenTitan validation using fixed fork
# Expected: 100% pass rate!

set -e

VERIBLE_BIN="${PWD}/bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax"
OPENTITAN_ROOT="/Users/jonguksong/Projects/opentitan-fork"

echo "================================================================"
echo "OpenTitan Full Validation - Fixed Fork"
echo "Expected: 100% success (all source bugs fixed!)"
echo "================================================================"
echo ""

# Find all SystemVerilog files
echo "Finding all SystemVerilog files..."
cd "${OPENTITAN_ROOT}"
find . -name "*.sv" -type f > /tmp/opentitan_all_files.txt
total=$(wc -l < /tmp/opentitan_all_files.txt | tr -d ' ')

echo "Found ${total} SystemVerilog files"
echo ""
echo "Running validation..."
echo ""

passed=0
failed=0
failed_files=""

while IFS= read -r file; do
    if "${VERIBLE_BIN}" "${file}" > /dev/null 2>&1; then
        ((passed++))
    else
        ((failed++))
        failed_files="${failed_files}${file}\n"
    fi
    
    # Progress indicator every 100 files
    current=$((passed + failed))
    if [ $((current % 100)) -eq 0 ]; then
        echo "Progress: ${current}/${total} files..."
    fi
done < /tmp/opentitan_all_files.txt

echo ""
echo "================================================================"
echo "RESULTS"
echo "================================================================"
echo "Total files:  ${total}"
echo "Passed:       ${passed}"
echo "Failed:       ${failed}"
echo ""

success_rate=$(awk "BEGIN {printf \"%.2f\", ($passed / $total) * 100}")
echo "Success rate: ${success_rate}%"
echo ""

if [ ${failed} -eq 0 ]; then
    echo "🎉🎉🎉 PERFECT! 100% SUCCESS! 🎉🎉🎉"
    echo ""
    echo "All OpenTitan files parse successfully with Verible v5.4.0!"
elif [ ${failed} -lt 35 ]; then
    echo "✅ EXCELLENT! ${success_rate}% success (was 99.00%)"
    echo ""
    echo "Improvement from fixes: +$(awk "BEGIN {printf \"%.2f\", $success_rate - 99.00}")%"
else
    echo "Still has ${failed} failures (expected ~33 remaining)"
fi

if [ ${failed} -gt 0 ]; then
    echo ""
    echo "Remaining failures:"
    echo -e "${failed_files}" | head -20
fi

echo ""
echo "================================================================"
