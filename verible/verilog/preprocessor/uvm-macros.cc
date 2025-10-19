// Copyright 2025 The Verible Authors.
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

// UVM Macro Registry Implementation
// Phase 2.2 of UVM Enhancement project
// 
// This provides stub macro definitions for common UVM macros.
// Phase 2.3 will add real expansion logic.

#include "verible/verilog/preprocessor/uvm-macros.h"

#include "verible/common/text/token-info.h"

namespace verilog {
namespace preprocessor {

// Helper to create a UVM macro with expansion body
// Phase 2.3: Basic macro expansion implementation
static verible::MacroDefinition CreateUvmMacro(
    std::string_view name, 
    const std::vector<std::string> &params,
    std::string_view body) {
  // Create token infos for macro definition
  verible::TokenInfo header_token(0, "");  // Placeholder header
  verible::TokenInfo name_token(0, name);
  verible::MacroDefinition macro(header_token, name_token);
  
  // Add parameters if any
  for (const auto &param : params) {
    verible::TokenInfo param_token(0, param);
    macro.AppendParameter(verible::MacroParameterInfo(param_token));
  }
  
  // Set macro body
  // Phase 2.3: Basic expansions for common patterns
  // Phase 2.4+: Will enhance with stringification and token pasting
  verible::TokenInfo body_token(0, body);
  macro.SetDefinitionText(body_token);
  
  return macro;
}

// Get the UVM macro registry
const std::map<std::string_view, verible::MacroDefinition>& GetUvmMacroRegistry() {
  // Static registry - initialized once
  // Note: Using static local variable to ensure proper initialization order
  static const auto *kUVMMacros = []() {
    auto *macros = new std::map<std::string_view, verible::MacroDefinition>();
    
    // Phase 2.3: Register UVM macros with basic expansion bodies
    // These are simplified versions that enable parsing
    // Full UVM functionality will be in actual UVM library
    
    // Object/Component Registration Macros
    // Note: Using minimal valid SystemVerilog that parsers can handle
    macros->emplace("uvm_object_utils", 
                    CreateUvmMacro("uvm_object_utils", {"TYPE"}, 
                                   "typedef TYPE type_id;"));
    
    macros->emplace("uvm_object_utils_begin",
                    CreateUvmMacro("uvm_object_utils_begin", {"TYPE"},
                                   "typedef TYPE type_id;"));
    
    macros->emplace("uvm_object_utils_end",
                    CreateUvmMacro("uvm_object_utils_end", {}, 
                                   ""));
    
    macros->emplace("uvm_component_utils",
                    CreateUvmMacro("uvm_component_utils", {"TYPE"},
                                   "typedef TYPE type_id;"));
    
    macros->emplace("uvm_component_utils_begin",
                    CreateUvmMacro("uvm_component_utils_begin", {"TYPE"},
                                   "typedef TYPE type_id;"));
    
    macros->emplace("uvm_component_utils_end",
                    CreateUvmMacro("uvm_component_utils_end", {}, 
                                   ""));
    
    // Field Automation Macros
    // Phase 2.3: Empty bodies - these are typically used inside begin/end pairs
    macros->emplace("uvm_field_int",
                    CreateUvmMacro("uvm_field_int", {"ARG", "FLAG"}, ""));
    macros->emplace("uvm_field_object",
                    CreateUvmMacro("uvm_field_object", {"ARG", "FLAG"}, ""));
    macros->emplace("uvm_field_string",
                    CreateUvmMacro("uvm_field_string", {"ARG", "FLAG"}, ""));
    macros->emplace("uvm_field_array_int",
                    CreateUvmMacro("uvm_field_array_int", {"ARG", "FLAG"}, ""));
    
    // Sequence Macros
    macros->emplace("uvm_do",
                    CreateUvmMacro("uvm_do", {"SEQ_OR_ITEM"}, "begin end"));
    macros->emplace("uvm_do_with",
                    CreateUvmMacro("uvm_do_with", {"SEQ_OR_ITEM", "CONSTRAINTS"}, 
                                   "begin end"));
    macros->emplace("uvm_sequence_utils",
                    CreateUvmMacro("uvm_sequence_utils", {"SEQUENCER"}, ""));
    
    // Reporting Macros
    // Expand to simple $display calls for parsing
    macros->emplace("uvm_info",
                    CreateUvmMacro("uvm_info", {"ID", "MSG", "VERBOSITY"}, 
                                   "$display(MSG);"));
    macros->emplace("uvm_warning",
                    CreateUvmMacro("uvm_warning", {"ID", "MSG"}, 
                                   "$display(MSG);"));
    macros->emplace("uvm_error",
                    CreateUvmMacro("uvm_error", {"ID", "MSG"}, 
                                   "$display(MSG);"));
    macros->emplace("uvm_fatal",
                    CreateUvmMacro("uvm_fatal", {"ID", "MSG"}, 
                                   "$display(MSG); $finish;"));
    
    // Factory Macros
    macros->emplace("uvm_object_param_utils",
                    CreateUvmMacro("uvm_object_param_utils", {"TYPE"},
                                   "typedef TYPE type_id;"));
    macros->emplace("uvm_object_param_utils_begin",
                    CreateUvmMacro("uvm_object_param_utils_begin", {"TYPE"},
                                   "typedef TYPE type_id;"));
    macros->emplace("uvm_component_param_utils",
                    CreateUvmMacro("uvm_component_param_utils", {"TYPE"},
                                   "typedef TYPE type_id;"));
    
    // Constructor Macro - very common in OpenTitan
    macros->emplace("uvm_object_new",
                    CreateUvmMacro("uvm_object_new", {},
                                   "function new(string name=\"\"); super.new(name); endfunction"));
    
    // OpenTitan DV Macros (from dv_macros.svh and cip_macros.svh)
    macros->emplace("DV_COMMON_CLK_CONSTRAINT",
                    CreateUvmMacro("DV_COMMON_CLK_CONSTRAINT", {"FREQ_"},
                                   "FREQ_ dist { [5:23] :/ 2, [24:25] :/ 2, [26:47] :/ 1, [48:50] :/ 2, [51:95] :/ 1, 96 :/ 1, [97:99] :/ 1, 100 :/ 1 };"));
    macros->emplace("gmv",
                    CreateUvmMacro("gmv", {"csr"},
                                   "csr.get_mirrored_value()"));
    macros->emplace("DV_MUBI8_DIST",
                    CreateUvmMacro("DV_MUBI8_DIST", {"VAR_", "T_WEIGHT_", "F_WEIGHT_", "OTHER_WEIGHT_"},
                                   ""));
    
    // Analysis Macros  
    macros->emplace("uvm_analysis_imp_decl",
                    CreateUvmMacro("uvm_analysis_imp_decl", {"SUFFIX"}, ""));
    
    // Callback Macros
    macros->emplace("uvm_register_cb",
                    CreateUvmMacro("uvm_register_cb", {"T", "CB"}, ""));
    macros->emplace("uvm_set_super_type",
                    CreateUvmMacro("uvm_set_super_type", {"TYPE", "SUPER"}, ""));
    
    // Phase Macros - these are typically function/task names
    macros->emplace("uvm_build_phase",
                    CreateUvmMacro("uvm_build_phase", {}, ""));
    macros->emplace("uvm_connect_phase",
                    CreateUvmMacro("uvm_connect_phase", {}, ""));
    macros->emplace("uvm_run_phase",
                    CreateUvmMacro("uvm_run_phase", {}, ""));
    
    // Config DB Macros
    macros->emplace("uvm_config_db",
                    CreateUvmMacro("uvm_config_db", {"T"}, ""));
    
    // TLM Macros
    macros->emplace("uvm_blocking_put_imp_decl",
                    CreateUvmMacro("uvm_blocking_put_imp_decl", {"SUFFIX"}, ""));
    macros->emplace("uvm_nonblocking_put_imp_decl",
                    CreateUvmMacro("uvm_nonblocking_put_imp_decl", {"SUFFIX"}, ""));
    
    return macros;
  }();
  
  return *kUVMMacros;
}

// Get list of complex UVM macros
const std::vector<std::string_view>& GetComplexUvmMacroNames() {
  static const std::vector<std::string_view> kComplexMacros = {
      "uvm_object_utils_begin",
      "uvm_object_utils_end",
      "uvm_component_utils_begin",
      "uvm_component_utils_end",
      "uvm_do_with",
  };
  return kComplexMacros;
}

}  // namespace preprocessor
}  // namespace verilog
