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

// Implementation of PackageContextResolver
// Feature 3 (v5.4.0): Package Context Mode
//
// GREEN PHASE: Full implementation

#include "verible/verilog/analysis/package-context-resolver.h"

#include <filesystem>
#include <memory>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "verible/common/analysis/syntax-tree-search.h"
#include "verible/common/text/concrete-syntax-tree.h"
#include "verible/common/text/symbol.h"
#include "verible/common/text/tree-utils.h"
#include "verible/common/util/file-util.h"
#include "verible/verilog/CST/verilog-matchers.h"  // IWYU pragma: keep
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/CST/package.h"
#include "verible/verilog/CST/class.h"
#include "verible/verilog/CST/type.h"
#include "verible/verilog/analysis/verilog-analyzer.h"
#include "verible/verilog/preprocessor/verilog-preprocess.h"

namespace verilog {

absl::StatusOr<PackageContext> PackageContextResolver::ParsePackage(
    std::string_view package_file) {
  PackageContext context;
  context.source_file = std::string(package_file);

  // Load the package file
  auto content_or = verible::file::GetContentAsMemBlock(std::string(package_file));
  if (!content_or.ok()) {
    return absl::NotFoundError(
        absl::StrCat("Package file not found: ", package_file));
  }

  // Create analyzer for the package
  // Include processing enabled to capture macros from include files
  VerilogPreprocess::Config preprocess_config{
      .filter_branches = false,
      .include_files = true,  // Enable to process `include directives in packages
      .expand_macros = false
  };

  // Set up file opener for includes
  VerilogAnalyzer::FileOpener file_opener = nullptr;
  if (include_resolver_) {
    file_opener = [this, package_file](std::string_view include_file) 
        -> absl::StatusOr<std::string_view> {
      return include_resolver_->ResolveInclude(include_file, package_file);
    };
  }

  // Wrap in shared_ptr as required by VerilogAnalyzer
  auto content_shared = std::shared_ptr<verible::MemBlock>(std::move(*content_or));
  
  auto analyzer = std::make_unique<VerilogAnalyzer>(
      content_shared, package_file, preprocess_config, file_opener);

  auto status = analyzer->Analyze();
  if (!status.ok()) {
    // Check if it's a preprocessor error (fatal) or syntax error (can continue)
    const auto& preprocess_data = analyzer->PreprocessorData();
    bool has_preprocessor_errors = !preprocess_data.errors.empty();
    
    if (has_preprocessor_errors) {
      // Preprocessor errors are fatal - can't extract macros
      for (const auto& error : preprocess_data.errors) {
        std::cerr << "Preprocessor error: " << error.error_message << std::endl;
      }
      return absl::InvalidArgumentError(
          absl::StrCat("Failed to parse package file: ", package_file,
                       " - Preprocessor error"));
    }
    
    // Syntax errors: Package parsed enough to extract macros, continue
    std::cerr << "Warning: Package " << package_file 
              << " has syntax errors, but macros will be extracted" << std::endl;
  }

  // Extract package name
  auto name_or = ExtractPackageName(*analyzer);
  if (name_or.ok()) {
    context.package_name = *name_or;
  }

  // Extract macros from preprocessor data
  auto extract_status = ExtractMacros(*analyzer, &context);
  if (!extract_status.ok()) {
    return extract_status;
  }

  // Extract type definitions
  extract_status = ExtractTypes(*analyzer, &context);
  if (!extract_status.ok()) {
    return extract_status;
  }

  // Extract import statements
  extract_status = ExtractImports(*analyzer, &context);
  if (!extract_status.ok()) {
    return extract_status;
  }

  // Store analyzer to keep memory alive for string_views in macro_definitions
  context.analyzer = std::move(analyzer);

  return context;
}

absl::StatusOr<CombinedPackageContext> PackageContextResolver::ParsePackages(
    const std::vector<std::string>& package_files) {
  CombinedPackageContext combined;

  for (const auto& package_file : package_files) {
    auto context_or = ParsePackage(package_file);
    if (!context_or.ok()) {
      return context_or.status();
    }

    PackageContext& context = *context_or;

    // Merge macros into combined context  
    // Move macros directly to avoid copy issues with MacroDefinition
    for (auto& [name, definition] : context.macro_definitions) {
      // Later packages override earlier ones
      auto it = combined.all_macros.find(name);
      if (it != combined.all_macros.end()) {
        combined.all_macros.erase(it);
      }
      combined.all_macros.emplace(name, std::move(definition));
    }

    // Merge types
    for (const auto& type_name : context.type_names) {
      combined.all_types.push_back(type_name);
    }

    combined.packages.push_back(std::move(context));
  }

  return combined;
}

absl::StatusOr<std::string> PackageContextResolver::AutoDetectPackageFile(
    std::string_view test_file) {
  std::filesystem::path test_path(test_file);
  
  // Get the directory containing the test file
  std::filesystem::path dir = test_path.parent_path();
  
  // Get the directory name
  std::string dir_name = dir.filename().string();
  
  // Try: <dir>/<dir>_pkg.sv
  std::filesystem::path pkg_file = dir / (dir_name + "_pkg.sv");
  
  if (std::filesystem::exists(pkg_file)) {
    return pkg_file.string();
  }

  // Try: <dir>/<dir>.sv (without _pkg suffix)
  pkg_file = dir / (dir_name + ".sv");
  if (std::filesystem::exists(pkg_file)) {
    return pkg_file.string();
  }

  return absl::NotFoundError(
      absl::StrCat("Could not auto-detect package file for: ", test_file,
                   " (looked in ", dir.string(), ")"));
}

// ===========================================================================
// Private Helper Methods
// ===========================================================================

absl::Status PackageContextResolver::ExtractMacros(
    const VerilogAnalyzer& analyzer,
    PackageContext* context) {
  // Get preprocessor data which contains macro definitions
  const auto& preprocess_data = analyzer.PreprocessorData();
  
  // Copy all macro definitions
  for (const auto& [name, definition] : preprocess_data.macro_definitions) {
    context->macro_definitions.insert({name, definition});
  }

  return absl::OkStatus();
}

absl::Status PackageContextResolver::ExtractTypes(
    const VerilogAnalyzer& analyzer,
    PackageContext* context) {
  const auto& syntax_tree = analyzer.SyntaxTree();
  if (!syntax_tree) {
    return absl::OkStatus();  // No syntax tree, no types
  }

  // Search for class declarations
  auto class_nodes = SearchSyntaxTree(*syntax_tree, NodekClassDeclaration());
  
  for (const auto& match : class_nodes) {
    // Extract class name using CST helper
    const auto* class_name_leaf = GetClassName(*match.match);
    if (class_name_leaf) {
      context->type_names.push_back(std::string(class_name_leaf->get().text()));
    }
  }

  // Search for typedef declarations
  auto typedef_nodes = SearchSyntaxTree(*syntax_tree, NodekTypeDeclaration());

  for (const auto& match : typedef_nodes) {
    // Extract typedef name - child 2 of kTypeDeclaration
    const auto* name_symbol = verible::GetSubtreeAsLeaf(*match.match, NodeEnum::kTypeDeclaration, 2);
    if (name_symbol) {
      context->type_names.push_back(std::string(name_symbol->get().text()));
    }
  }

  return absl::OkStatus();
}

absl::Status PackageContextResolver::ExtractImports(
    const VerilogAnalyzer& analyzer,
    PackageContext* context) {
  const auto& syntax_tree = analyzer.SyntaxTree();
  if (!syntax_tree) {
    return absl::OkStatus();
  }

  // Search for package import items (not just declarations)
  auto import_items = SearchSyntaxTree(*syntax_tree, NodekPackageImportItem());

  for (const auto& match : import_items) {
    // Extract imported package name using CST helper
    const auto* package_name_leaf = GetImportedPackageName(*match.match);
    if (package_name_leaf) {
      std::string pkg_name(package_name_leaf->get().text());
      
      // Check if we're importing a specific item or wildcard
      const auto* item_name = GeImportedItemNameFromPackageImportItem(*match.match);
      if (item_name) {
        // Specific import: "pkg::item"
        context->imports.push_back(pkg_name + "::" + std::string(item_name->get().text()));
      } else {
        // Wildcard import: "pkg::*"
        context->imports.push_back(pkg_name + "::*");
      }
    }
  }

  return absl::OkStatus();
}

absl::StatusOr<std::string> PackageContextResolver::ExtractPackageName(
    const VerilogAnalyzer& analyzer) {
  const auto& syntax_tree = analyzer.SyntaxTree();
  if (!syntax_tree) {
    return absl::NotFoundError("No syntax tree available");
  }

  // Search for package declaration
  auto package_nodes = SearchSyntaxTree(*syntax_tree, NodekPackageDeclaration());

  if (package_nodes.empty()) {
    return absl::NotFoundError("No package declaration found");
  }

  // Extract package name using CST helper
  const auto* package_name_token = GetPackageNameToken(*package_nodes[0].match);
  if (!package_name_token) {
    return absl::NotFoundError("Could not extract package name from declaration");
  }

  return std::string(package_name_token->text());
}

}  // namespace verilog

