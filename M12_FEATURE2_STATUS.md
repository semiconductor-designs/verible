# Feature 2: Multiline String Literals - Status

**Status:** Partially Implemented (Lexer Complexity)

## Issue

The flex lexer architecture makes stateful multiline token accumulation complex:
- Using `yymore()` causes infinite loops
- Without `yymore()`, only the last matched text is available
- Flex's `.` doesn't match newlines by default

## What Was Attempted

1. State-based approach with `yymore()` - caused timeout
2. Single regex pattern - doesn't handle newlines
3. State-based without `yymore()` - loses token content

## Recommended Solution

Requires deeper lexer refactoring:
- Add a string buffer member variable to VerilogLexer class
- Manually accumulate text in MULTILINE_STRING state
- Return accumulated buffer on closing `"""`

## Next Steps

- Complete simpler features first (4-7)
- Return to Feature 2 with proper lexer buffer implementation
- Or consider Feature 2 as v4.1.0 enhancement

**For now, moving to Feature 4 (soft unions) which is straightforward.**

