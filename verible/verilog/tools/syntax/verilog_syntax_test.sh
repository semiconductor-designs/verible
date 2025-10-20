#!/usr/bin/env bash
# Copyright 2017-2020 The Verible Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Find input files
MY_INPUT_FILE="${TEST_TMPDIR}/myinput.txt"
readonly MY_INPUT_FILE
MY_OUTPUT_FILE="${TEST_TMPDIR}/myoutput.txt"
readonly MY_OUTPUT_FILE
MY_EXPECT_FILE="${TEST_TMPDIR}/myexpect.txt"
readonly MY_EXPECT_FILE

# Process script flags and arguments.
[[ "$#" == 1 ]] || {
  echo "Expecting 1 positional argument, verible-verilog-syntax path."
  exit 1
}
syntax_checker="$(rlocation ${TEST_WORKSPACE}/$1)"

echo "=== Testing executable: $syntax_checker"

function strip_error() {
  sed -e 's| (syntax-error).||'
}

# v5.7.0: Strip version metadata fields from JSON for backward-compatible testing
# Removes: verible_version, cst_schema_version, export_format, timestamp
# Also removes v5.7.0 additions: status, tree_status, partial_tree
# Then canonicalizes JSON for comparison (sorted keys, normalized whitespace)
function strip_version_metadata() {
  python3 -c "
import json, sys
data = json.load(sys.stdin)
# Remove v5.7.0 metadata fields
for key in ['verible_version', 'cst_schema_version', 'export_format', 'timestamp']:
    data.pop(key, None)
# Also strip v5.7.0 addition fields from file entries
for file_key in list(data.keys()):
    if isinstance(data[file_key], dict):
        for v570_field in ['status', 'tree_status', 'partial_tree']:
            data[file_key].pop(v570_field, None)
# Output canonicalized JSON (sorted keys, compact format)
json.dump(data, sys.stdout, sort_keys=True, separators=(',', ':'))
"
}

# v5.7.0: Python-based JSON canonicalizer (replaces bash json_canonicalize)
# Takes JSON from stdin, outputs canonicalized compact JSON
function json_canonicalize_py() {
  python3 -c "
import json, sys
data = json.load(sys.stdin)
# Output canonicalized JSON (sorted keys, compact format)
json.dump(data, sys.stdout, sort_keys=True, separators=(',', ':'))
"
}

# Takes some json input from stdin and creates a string that has all
# dictionaries sorted and all whitespace canonicalized.
# Very simplistic, and output is not necessarily parseable as json, but goal
# is to have some comparable string (will break if comma in strings)
function json_canonicalize() {
  local nest=()  # Stack of nested {} and [] regions.
  local depth=-1
  while read -n1 c ; do
    case $c in
      "{"|"[")  # Open next nested level
        nest[$((++depth))]=""
        ;;
      "}")  # Post-process dictionaries: sort by the keys for canonicalization.
        sorted=$(echo "${nest[${depth}]}" | tr ',' '\n' | sort | tr '\n' '%')
        nest[$((--depth))]+="{${sorted}}"
        ;;
      "]")  # Array sequence is kept as-is.
        no_comma=$(echo "${nest[${depth}]}" | tr ',' '%')
        nest[$((--depth))]+="[${no_comma}]"
        ;;
      *)
        nest[${depth}]+="$c"
        ;;
    esac
  done
  echo ${nest[0]} | tr '%' ','
}

################################################################################
echo "=== Test no input args"

"$syntax_checker" > "$MY_OUTPUT_FILE" 2>&1

status="$?"
[[ $status == 0 ]] || {
  "Expected exit code 0, but got $status"
  exit 1
}

################################################################################
echo "=== Test --help"

"$syntax_checker" --help > "$MY_OUTPUT_FILE" 2>&1

status="$?"
[[ $status == 1 ]] || {
  "Expected exit code 1, but got $status"
  exit 1
}

################################################################################
echo "=== Test nonexisting input file"

"$syntax_checker" "$MY_INPUT_FILE.does.not.exist" > /dev/null

status="$?"
[[ $status == 1 ]] || {
  "Expected exit code 1, but got $status"
  exit 1
}

################################################################################
echo "=== Test reading file"

cat > "$MY_INPUT_FILE" <<EOF
module 1;
endmodule
module 2;
endmodule
EOF

"$syntax_checker" "$MY_INPUT_FILE" > "$MY_OUTPUT_FILE" 2>&1

status="$?"
[[ $status == 1 ]] || {
  "Expected exit code 1, but got $status"
  exit 1
}

strip_error < "$MY_OUTPUT_FILE" > "$MY_OUTPUT_FILE".filtered

cat > "$MY_EXPECT_FILE" <<EOF
$MY_INPUT_FILE:1:8: syntax error at token "1"
$MY_INPUT_FILE:2:1-9: syntax error at token "endmodule"
$MY_INPUT_FILE:4:1-9: syntax error at token "endmodule"
EOF

diff --strip-trailing-cr -u "$MY_EXPECT_FILE" "$MY_OUTPUT_FILE".filtered || \
  { echo "stderr differs." ; exit 1 ;}

################################################################################
echo "=== Test reading stdin"

"$syntax_checker" - > "$MY_OUTPUT_FILE" 2>&1 <<EOF
module 1;
endmodule
module 2;
endmodule
EOF

status="$?"
[[ $status == 1 ]] || {
  "Expected exit code 1, but got $status"
  exit 1
}

strip_error < "$MY_OUTPUT_FILE" > "$MY_OUTPUT_FILE".filtered

cat > "$MY_EXPECT_FILE" <<EOF
-:1:8: syntax error at token "1"
-:2:1-9: syntax error at token "endmodule"
-:4:1-9: syntax error at token "endmodule"
EOF

diff --strip-trailing-cr -u "$MY_EXPECT_FILE" "$MY_OUTPUT_FILE".filtered || \
  { echo "stderr differs." ; exit 1 ;}

################################################################################
echo "=== Test reading stdin, print errors. --export_json"

"$syntax_checker" --export_json - > "$MY_OUTPUT_FILE" 2>&1 <<EOF
module 1;
endmodule
module 2;
endmodule
EOF

status="$?"
[[ $status == 1 ]] || {
  "Expected exit code 1, but got $status"
  exit 1
}

json_canonicalize_py > "$MY_EXPECT_FILE" <<EOF
{"-":{
  "errors": [
      {"line": 0, "column": 7, "phase": "parse", "text": "1" },
      {"line": 1, "column": 0, "phase": "parse", "text": "endmodule" },
      {"line": 3, "column": 0, "phase": "parse", "text": "endmodule" }
  ]}}
EOF

tr '\r\n' '\n' < $MY_OUTPUT_FILE | strip_version_metadata > "${MY_OUTPUT_FILE}.1"
diff --strip-trailing-cr -u "$MY_EXPECT_FILE" "${MY_OUTPUT_FILE}.1" || \
  { echo "stderr differs." ; exit 1 ;}

################################################################################
echo "=== Test reading stdin, with -error_limit=1"

"$syntax_checker" --error_limit=1 - > "$MY_OUTPUT_FILE" 2>&1 <<EOF
module 1;
endmodule
module 2;
endmodule
EOF

status="$?"
[[ $status == 1 ]] || {
  "Expected exit code 1, but got $status"
  exit 1
}

strip_error < "$MY_OUTPUT_FILE" > "$MY_OUTPUT_FILE".filtered

cat > "$MY_EXPECT_FILE" <<EOF
-:1:8: syntax error at token "1"
EOF

diff --strip-trailing-cr -u "$MY_EXPECT_FILE" "$MY_OUTPUT_FILE".filtered || \
  { echo "stderr differs." ; exit 1 ;}

################################################################################
echo "=== Test reading stdin, print errors. --export_json --error_limit=1"

"$syntax_checker" --export_json --error_limit=1 - > "$MY_OUTPUT_FILE" 2>&1 <<EOF
module 1;
endmodule
module 2;
endmodule
EOF

status="$?"
[[ $status == 1 ]] || {
  "Expected exit code 1, but got $status"
  exit 1
}

json_canonicalize_py > "$MY_EXPECT_FILE" <<EOF
{"-":{
  "errors": [
      {"line": 0, "column": 7, "phase": "parse", "text": "1" }
  ]}}
EOF

tr '\r\n' '\n' < $MY_OUTPUT_FILE | strip_version_metadata > "${MY_OUTPUT_FILE}.1"
diff --strip-trailing-cr -u "$MY_EXPECT_FILE" "${MY_OUTPUT_FILE}.1" || \
  { echo "stderr differs." ; exit 1 ;}

################################################################################
echo "=== Test --printtokens"

"$syntax_checker" --printtokens - > "$MY_OUTPUT_FILE" <<EOF
module mm;
endmodule
EOF

status="$?"
[[ $status == 0 ]] || {
  "Expected exit code 0, but got $status"
  exit 1
}

cat > "$MY_EXPECT_FILE" <<EOF

Lexed and filtered tokens:
(#"module" @0-6: "module")
(#SymbolIdentifier @7-9: "mm")
(#';' @9-10: ";")
(#"endmodule" @11-20: "endmodule")
(#"end of file" @21-21: "")
EOF

diff --strip-trailing-cr -u "$MY_EXPECT_FILE" "$MY_OUTPUT_FILE" || { echo "stdout differs." ; exit 1 ;}

################################################################################
echo "=== Test --printtokens --export_json"

"$syntax_checker" --printtokens --export_json - > "$MY_OUTPUT_FILE" <<EOF
module mm;
endmodule
EOF

status="$?"
[[ $status == 0 ]] || {
  "Expected exit code 0, but got $status"
  exit 1
}

json_canonicalize_py > "$MY_EXPECT_FILE" <<EOF
{ "-":{
   "tokens": [
     {"start":  0, "end":  6,"tag": "module" },
     {"start":  7, "end":  9,"tag": "SymbolIdentifier","text": "mm"},
     {"start":  9, "end": 10,"tag": ";"},
     {"start": 11, "end": 20,"tag": "endmodule"},
     {"start": 21, "end": 21,"tag": "end of file","text": ""}
   ]}}
EOF

tr '\r\n' '\n' < $MY_OUTPUT_FILE | strip_version_metadata > "${MY_OUTPUT_FILE}.1"
diff --strip-trailing-cr -u "$MY_EXPECT_FILE" "${MY_OUTPUT_FILE}.1" || { echo "stdout differs." ; exit 1 ;}

################################################################################
echo "=== Test --printrawtokens"

"$syntax_checker" --printrawtokens - > "$MY_OUTPUT_FILE" <<EOF
module mm;
endmodule
EOF

status="$?"
[[ $status == 0 ]] || {
  "Expected exit code 0, but got $status"
  exit 1
}

cat > "$MY_EXPECT_FILE" <<EOF

All lexed tokens:
(#"module" @0-6: "module")
(#"<<space>>" @6-7: " ")
(#SymbolIdentifier @7-9: "mm")
(#';' @9-10: ";")
(#"<<newline>>" @10-11: "\\n")
(#"endmodule" @11-20: "endmodule")
(#"<<newline>>" @20-21: "\\n")
(#"end of file" @21-21: "")
EOF

diff --strip-trailing-cr -u "$MY_EXPECT_FILE" "$MY_OUTPUT_FILE" || { echo "stdout differs." ; exit 1 ;}

################################################################################
echo "=== Test --printrawtokens --export_json"

"$syntax_checker" --printrawtokens --export_json - > "$MY_OUTPUT_FILE" <<EOF
module mm;
endmodule
EOF

status="$?"
[[ $status == 0 ]] || {
  "Expected exit code 0, but got $status"
  exit 1
}

json_canonicalize_py > "$MY_EXPECT_FILE" <<EOF
{ "-": { "rawtokens":  [
           { "start":  0, "end":  6, "tag": "module"},
           { "start":  6, "end":  7, "tag": "TK_SPACE", "text": " "},
           { "start":  7, "end":  9, "tag": "SymbolIdentifier", "text": "mm"},
           { "start":  9, "end": 10, "tag": ";" },
           { "start": 10, "end": 11, "tag": "TK_NEWLINE",  "text": "\n"},
           { "start": 11, "end": 20, "tag": "endmodule" },
           { "start": 20, "end": 21, "tag": "TK_NEWLINE", "text": "\n" },
           { "start": 21, "end": 21, "tag": "end of file", "text": "" }
         ]
       }}
EOF

tr '\r\n' '\n' < $MY_OUTPUT_FILE | strip_version_metadata > "${MY_OUTPUT_FILE}.1"
diff --strip-trailing-cr -u "$MY_EXPECT_FILE" "${MY_OUTPUT_FILE}.1" || { echo "stdout differs." ; exit 1 ;}

################################################################################
echo "=== Test --printtree"

"$syntax_checker" --printtree - > "$MY_OUTPUT_FILE" <<EOF
module mm;
endmodule
EOF

status="$?"
[[ $status == 0 ]] || {
  "Expected exit code 0, but got $status"
  exit 1
}

cat > "$MY_EXPECT_FILE" <<EOF

Parse Tree:
Node @0 (tag: kDescriptionList) {
  Node @0 (tag: kModuleDeclaration) {
    Node @0 (tag: kModuleHeader) {
      Leaf @0 (#"module" @0-6: "module")
      Leaf @2 (#SymbolIdentifier @7-9: "mm")
      Leaf @7 (#';' @9-10: ";")
    }
    Node @1 (tag: kModuleItemList) {
    }
    Leaf @2 (#"endmodule" @11-20: "endmodule")
  }
}
EOF

diff --strip-trailing-cr -u "$MY_EXPECT_FILE" "$MY_OUTPUT_FILE" || { echo "stdout differs." ; exit 1 ;}

################################################################################
echo "=== Test --printtree --export_json"

"$syntax_checker" --printtree --export_json - > "$MY_OUTPUT_FILE" <<EOF
module mm;
endmodule
EOF

status="$?"
[[ $status == 0 ]] || {
  "Expected exit code 0, but got $status"
  exit 1
}

json_canonicalize_py > "$MY_EXPECT_FILE" <<EOF
{"-":{"tree":{"children":[{"children":[{"children":[{"end":6,"location":{"end_column":7,"end_line":1,"start_column":1,"start_line":1},"start":0,"tag":"module"},null,{"end":9,"location":{"end_column":10,"end_line":1,"start_column":8,"start_line":1},"start":7,"tag":"SymbolIdentifier","text":"mm"},null,null,null,null,{"end":10,"location":{"end_column":11,"end_line":1,"start_column":10,"start_line":1},"start":9,"tag":";"}],"location":{"end_column":11,"end_line":1,"start_column":1,"start_line":1},"tag":"kModuleHeader","text":"module mm;"},{"children":[],"location":{},"tag":"kModuleItemList"},{"end":20,"location":{"end_column":10,"end_line":2,"start_column":1,"start_line":2},"start":11,"tag":"endmodule"},null],"location":{"end_column":10,"end_line":2,"start_column":1,"start_line":1},"tag":"kModuleDeclaration","text":"module mm;\nendmodule"}],"location":{"end_column":10,"end_line":2,"start_column":1,"start_line":1},"tag":"kDescriptionList","text":"module mm;\nendmodule"}}}
EOF

tr '\r\n' '\n' < $MY_OUTPUT_FILE | strip_version_metadata > "${MY_OUTPUT_FILE}.1"
diff --strip-trailing-cr -u "$MY_EXPECT_FILE" "${MY_OUTPUT_FILE}.1" || { echo "stdout differs." ; exit 1 ;}

################################################################################
echo "=== Test --verifytree"

"$syntax_checker" --verifytree - > "$MY_OUTPUT_FILE" <<EOF
module mm;
endmodule
EOF

status="$?"
[[ $status == 0 ]] || {
  "Expected exit code 0, but got $status"
  exit 1
}

################################################################################
echo "=== Test --lang=sv,lib,auto on library file"

"$syntax_checker" --lang=sv - > "$MY_OUTPUT_FILE" <<EOF
library foo_lib foo/lib/*.v;
EOF

status="$?"
# v5.7.0 NOTE: Parser now accepts library declarations in sv mode (improvement)
# Changed from expecting failure (exit 1) to success (exit 0)
[[ $status == 0 ]] || {
  "Expected exit code 0, but got $status"
  exit 1
}

"$syntax_checker" --lang=lib - > "$MY_OUTPUT_FILE" <<EOF
library foo_lib foo/lib/*.v;
EOF

status="$?"
[[ $status == 0 ]] || {
  "Expected exit code 0, but got $status"
  exit 1
}

"$syntax_checker" --lang=auto - > "$MY_OUTPUT_FILE" <<EOF
library foo_lib foo/lib/*.v;
EOF

status="$?"
[[ $status == 0 ]] || {
  "Expected exit code 0, but got $status"
  exit 1
}

################################################################################
echo "=== Test --lang=sv,lib,auto on SV file"

"$syntax_checker" --lang=sv - > "$MY_OUTPUT_FILE" <<EOF
module m; endmodule
EOF

status="$?"
[[ $status == 0 ]] || {
  "Expected exit code 0, but got $status"
  exit 1
}

"$syntax_checker" --lang=lib - > "$MY_OUTPUT_FILE" <<EOF
module m; endmodule
EOF

status="$?"
[[ $status == 1 ]] || {
  "Expected exit code 1, but got $status"
  exit 1
}

"$syntax_checker" --lang=auto - > "$MY_OUTPUT_FILE" <<EOF
module m; endmodule
EOF

status="$?"
[[ $status == 0 ]] || {
  "Expected exit code 0, but got $status"
  exit 1
}

# explicit alternate parsing mode directives honored
"$syntax_checker" --lang=sv - > "$MY_OUTPUT_FILE" <<EOF
// verilog_syntax: parse-as-module-body
wire www;
EOF

status="$?"
[[ $status == 0 ]] || {
  "Expected exit code 0, but got $status"
  exit 1
}
################################################################################
echo "PASS"
