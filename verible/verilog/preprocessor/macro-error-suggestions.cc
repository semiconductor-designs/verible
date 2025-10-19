// Copyright 2017-2020 The Verible Authors.
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

#include "verible/verilog/preprocessor/macro-error-suggestions.h"

#include <algorithm>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

namespace verilog {

// Check if macro name matches UVM pattern
bool IsKnownUVMMacro(std::string_view macro_name) {
  // UVM macros typically start with "uvm_"
  if (macro_name.substr(0, 4) == "uvm_") {
    return true;
  }
  
  // Common UVM macros
  const std::vector<std::string_view> known_uvm_macros = {
      "uvm_object_utils", "uvm_object_utils_begin", "uvm_object_utils_end",
      "uvm_component_utils", "uvm_component_utils_begin", "uvm_component_utils_end",
      "uvm_field_int", "uvm_field_object", "uvm_field_string",
      "uvm_field_enum", "uvm_field_array_int", "uvm_field_queue",
      "uvm_info", "uvm_warning", "uvm_error", "uvm_fatal",
      "uvm_do", "uvm_do_with", "uvm_send",
      "uvm_object_new", "uvm_sequence_utils", "uvm_sequencer_utils"
  };
  
  return std::find(known_uvm_macros.begin(), known_uvm_macros.end(), macro_name) 
         != known_uvm_macros.end();
}

// Check if macro name matches OpenTitan pattern
bool IsKnownOpenTitanMacro(std::string_view macro_name) {
  // OpenTitan macros typically start with "DV_" or specific patterns
  if (macro_name.substr(0, 3) == "DV_") {
    return true;
  }
  
  // Common OpenTitan macros
  const std::vector<std::string_view> known_ot_macros = {
      "DV_CHECK", "DV_CHECK_FATAL", "DV_CHECK_STD_RANDOMIZE_FATAL",
      "DV_CHECK_RANDOMIZE_FATAL", "DV_CHECK_EQ", "DV_CHECK_NE",
      "DV_COMMON_CLK_CONSTRAINT", "DV_MUBI4_DIST", "DV_MUBI8_DIST",
      "gmv", "gfv", "grv"  // get_mirrored_value, get_field_value, get_reg_value
  };
  
  return std::find(known_ot_macros.begin(), known_ot_macros.end(), macro_name) 
         != known_ot_macros.end();
}

// Suggest package file based on current file path
std::string SuggestPackageFile(std::string_view current_file) {
  // Look for patterns like: path/to/module_name.sv
  // Suggest: path/to/module_name_pkg.sv
  
  std::string file_str(current_file);
  
  // Find the directory and basename
  size_t last_slash = file_str.find_last_of("/\\");
  std::string dir = (last_slash != std::string::npos) 
                    ? file_str.substr(0, last_slash + 1) 
                    : "";
  std::string basename = (last_slash != std::string::npos) 
                         ? file_str.substr(last_slash + 1) 
                         : file_str;
  
  // Remove .sv extension
  size_t dot_pos = basename.rfind(".sv");
  if (dot_pos != std::string::npos) {
    basename = basename.substr(0, dot_pos);
  }
  
  // Common patterns:
  // 1. module_env.sv -> module_env_pkg.sv
  // 2. module_component.sv -> module_pkg.sv (remove component suffix)
  // 3. module.sv -> module_pkg.sv
  
  std::string pkg_basename = basename;
  
  // Remove common suffixes
  const std::vector<std::string> suffixes = {
      "_env", "_agent", "_driver", "_monitor", "_scoreboard",
      "_sequencer", "_sequence", "_config", "_cov", "_class"
  };
  
  for (const auto& suffix : suffixes) {
    size_t pos = pkg_basename.rfind(suffix);
    if (pos != std::string::npos && pos + suffix.length() == pkg_basename.length()) {
      pkg_basename = pkg_basename.substr(0, pos);
      break;
    }
  }
  
  return dir + pkg_basename + "_pkg.sv";
}

// Generate enhanced error message with suggestions
std::string GetMacroErrorWithSuggestions(
    std::string_view macro_name,
    std::string_view current_file,
    const std::vector<std::string>& include_paths) {
  
  std::ostringstream error_msg;
  error_msg << "Error expanding macro `" << macro_name 
            << "': macro not defined.\n";
  
  // Check if it's a known UVM macro
  if (IsKnownUVMMacro(macro_name)) {
    error_msg << "\n";
    error_msg << "  This appears to be a UVM macro. Solutions:\n";
    error_msg << "  1. Add UVM include path:\n";
    error_msg << "     --include_paths=third_party/uvm/src\n";
    error_msg << "\n";
    error_msg << "  2. Or parse the package file that includes UVM macros:\n";
    std::string pkg_file = SuggestPackageFile(current_file);
    error_msg << "     verible-verilog-syntax --include_paths=third_party/uvm/src "
              << pkg_file << "\n";
    return error_msg.str();
  }
  
  // Check if it's a known OpenTitan macro
  if (IsKnownOpenTitanMacro(macro_name)) {
    error_msg << "\n";
    error_msg << "  This appears to be an OpenTitan DV macro. Solutions:\n";
    error_msg << "  1. Add OpenTitan include paths:\n";
    error_msg << "     --include_paths=third_party/uvm/src,hw/dv/sv/dv_utils,hw/dv/sv/cip_lib\n";
    error_msg << "\n";
    error_msg << "  2. Or parse the package file:\n";
    std::string pkg_file = SuggestPackageFile(current_file);
    error_msg << "     verible-verilog-syntax --include_paths=... " << pkg_file << "\n";
    return error_msg.str();
  }
  
  // Generic suggestions for unknown macros
  error_msg << "\n";
  error_msg << "  Possible solutions:\n";
  error_msg << "  1. Check if the macro is defined in an include file\n";
  error_msg << "     Add: --include_paths=/path/to/includes\n";
  error_msg << "\n";
  error_msg << "  2. This file may be part of a package. Try parsing the package file:\n";
  std::string pkg_file = SuggestPackageFile(current_file);
  error_msg << "     " << pkg_file << "\n";
  error_msg << "\n";
  error_msg << "  3. Define the macro on command line (v5.4.0+):\n";
  error_msg << "     --define=" << macro_name << "=value\n";
  
  if (!include_paths.empty()) {
    error_msg << "\n";
    error_msg << "  Current include paths:\n";
    for (const auto& path : include_paths) {
      error_msg << "    - " << path << "\n";
    }
  }
  
  return error_msg.str();
}

}  // namespace verilog

