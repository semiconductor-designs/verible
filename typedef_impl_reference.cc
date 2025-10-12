// Reference implementation for BuildTypedefTable
// This will be integrated into verilog-tree-json.cc in stages

// Helper: Build a typedef table from the syntax tree
static std::unordered_map<std::string, TypedefInfo> BuildTypedefTable(
    const verible::Symbol& root, std::string_view source_text) {
  std::unordered_map<std::string, TypedefInfo> typedef_table;
  
  // Find all typedef declarations
  auto typedef_matches = verible::SearchSyntaxTree(root, NodekTypeDeclaration());
  
  for (const auto& match : typedef_matches) {
    const auto* typedef_node = match.match;
    if (!typedef_node || typedef_node->Kind() != verible::SymbolKind::kNode) continue;
    
    const auto& node = verible::SymbolCastToNode(*typedef_node);
    
    // Get typedef name (child 2)
    const verible::Symbol* name_symbol = GetSubtreeAsSymbol(node, NodeEnum::kTypeDeclaration, 2);
    if (!name_symbol || name_symbol->Kind() != verible::SymbolKind::kLeaf) continue;
    const auto& name_leaf = verible::SymbolCastToLeaf(*name_symbol);
    std::string typedef_name(name_leaf.get().text());
    
    // Get referenced type (child 1 - kDataType)
    const verible::Symbol* ref_type = GetSubtreeAsSymbol(node, NodeEnum::kTypeDeclaration, 1);
    if (!ref_type) continue;
    
    // Initialize TypedefInfo
    TypedefInfo info;
    info.typedef_name = typedef_name;
    info.is_signed = false;
    info.is_packed = false;
    info.is_enum = false;
    info.enum_member_count = 0;
    info.is_struct = false;
    info.struct_field_count = 0;
    info.is_union = false;
    info.union_member_count = 0;
    info.is_parameterized = false;
    info.is_array = false;
    info.array_dimensions = 0;
    info.resolution_depth = 1;
    info.definition_line = -1;
    info.definition_column = -1;
    info.dimension_string = "";
    info.width = 0;
    
    // Extract source location from typedef declaration
    std::string_view node_text = verible::StringSpanOfSymbol(node);
    if (!source_text.empty() && node_text.data() >= source_text.data() && 
        node_text.data() < source_text.data() + source_text.size()) {
      size_t offset = node_text.data() - source_text.data();
      int line = 1, column = 1;
      for (size_t i = 0; i < offset && i < source_text.size(); ++i) {
        if (source_text[i] == '\n') {
          line++;
          column = 1;
        } else {
          column++;
        }
      }
      info.definition_line = line;
      info.definition_column = column;
    }
    
    // Get base type - BASIC VERSION (will be enhanced for enum/struct/union)
    const verible::Symbol* base_type_symbol = GetBaseTypeFromDataType(*ref_type);
    if (base_type_symbol) {
      if (base_type_symbol->Kind() == verible::SymbolKind::kLeaf) {
        const auto& base_leaf = verible::SymbolCastToLeaf(*base_type_symbol);
        info.base_type = std::string(base_leaf.get().text());
      } else if (base_type_symbol->Kind() == verible::SymbolKind::kNode) {
        const auto& base_node = verible::SymbolCastToNode(*base_type_symbol);
        
        if (base_node.MatchesTag(NodeEnum::kDataTypePrimitive)) {
          const verible::Symbol* prim_child = GetSubtreeAsSymbol(base_node, NodeEnum::kDataTypePrimitive, 0);
          if (prim_child && prim_child->Kind() == verible::SymbolKind::kLeaf) {
            const auto& prim_leaf = verible::SymbolCastToLeaf(*prim_child);
            info.base_type = std::string(prim_leaf.get().text());
          } else if (prim_child && prim_child->Kind() == verible::SymbolKind::kNode) {
            const auto& prim_child_node = verible::SymbolCastToNode(*prim_child);
            // Check for typedef reference (kUnqualifiedId)
            if (prim_child_node.MatchesTag(NodeEnum::kUnqualifiedId)) {
              std::string_view id_text = verible::StringSpanOfSymbol(prim_child_node);
              info.base_type = std::string(id_text);
            }
          }
        }
      }
    }
    
    // Build resolved type string
    if (!info.base_type.empty()) {
      info.resolved_type_string = info.base_type;
    }
    
    // Store in table
    typedef_table[typedef_name] = info;
  }
  
  return typedef_table;
}

