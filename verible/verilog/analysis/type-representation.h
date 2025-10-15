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

#ifndef VERIBLE_VERILOG_ANALYSIS_TYPE_REPRESENTATION_H_
#define VERIBLE_VERILOG_ANALYSIS_TYPE_REPRESENTATION_H_

#include <string>
#include <vector>

namespace verilog {
namespace analysis {

// SystemVerilog primitive types
enum class PrimitiveType {
  // 2-state types
  kBit,
  kLogic,
  kReg,
  
  // 4-state types
  kInteger,
  kInt,
  kShortInt,
  kLongInt,
  kByte,
  
  // Real types
  kReal,
  kRealTime,
  kShortReal,
  
  // String and other types
  kString,
  kChandle,
  kEvent,
  
  // Net types
  kWire,
  kTri,
  kSupply0,
  kSupply1,
  
  // Special types
  kVoid,
  kUserDefined,  // For user-defined types (structs, enums, classes)
  kUnknown,
};

// Represents a SystemVerilog type
struct Type {
  PrimitiveType base_type = PrimitiveType::kUnknown;
  
  // Type modifiers
  bool is_signed = false;
  bool is_packed = false;
  bool is_const = false;
  
  // Dimensions: [7:0] = {8}, [3:0][7:0] = {4, 8}
  std::vector<int> dimensions;
  
  // For user-defined types (structs, enums, classes, typedefs)
  std::string user_type_name;
  
  // Constructors
  Type() = default;
  Type(PrimitiveType type) : base_type(type) {}
  Type(PrimitiveType type, int width)
      : base_type(type), dimensions({width}) {}
  
  // Convert type to string representation
  std::string ToString() const;
  
  // Check if this type can accept a value of 'other' type
  // Returns true if assignment is valid (possibly with warnings)
  bool IsAssignableFrom(const Type& other) const;
  
  // Type properties
  bool IsNumeric() const;
  bool IsIntegral() const;
  bool Is2State() const;
  bool Is4State() const;
  bool IsReal() const;
  bool IsNet() const;
  bool IsUnknown() const { return base_type == PrimitiveType::kUnknown; }
  bool IsString() const { return base_type == PrimitiveType::kString; }
  bool IsUserDefined() const { return base_type == PrimitiveType::kUserDefined; }
  
  // Get bit width of the type
  int GetWidth() const;
  
  // Comparison operators
  bool operator==(const Type& other) const;
  bool operator!=(const Type& other) const { return !(*this == other); }
};

// Helper functions for type creation
Type MakeLogicType(int width, bool is_signed = false);
Type MakeBitType(int width, bool is_signed = false);
Type MakeIntType();
Type MakeRealType();
Type MakeStringType();
Type MakeUserDefinedType(const std::string& name);

// Get string representation of PrimitiveType
std::string PrimitiveTypeToString(PrimitiveType type);

}  // namespace analysis
}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_TYPE_REPRESENTATION_H_

