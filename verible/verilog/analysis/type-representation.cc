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

#include "verible/verilog/analysis/type-representation.h"

#include <sstream>
#include <string>

namespace verilog {
namespace analysis {

std::string Type::ToString() const {
  std::ostringstream oss;
  
  // Add signedness
  if (is_signed && IsIntegral()) {
    oss << "signed ";
  }
  
  // Add packed qualifier
  if (is_packed) {
    oss << "packed ";
  }
  
  // Add const qualifier
  if (is_const) {
    oss << "const ";
  }
  
  // Add base type
  if (base_type == PrimitiveType::kUserDefined) {
    oss << user_type_name;
  } else {
    oss << PrimitiveTypeToString(base_type);
  }
  
  // Add dimensions
  for (int dim : dimensions) {
    oss << "[" << (dim - 1) << ":0]";
  }
  
  return oss.str();
}

bool Type::IsAssignableFrom(const Type& other) const {
  // Unknown types are not assignable
  if (IsUnknown() || other.IsUnknown()) {
    return false;
  }
  
  // 1. Exact match
  if (*this == other) {
    return true;
  }
  
  // 2. String assignments
  if (base_type == PrimitiveType::kString) {
    return other.base_type == PrimitiveType::kString;
  }
  
  // 3. Numeric conversions
  if (IsNumeric() && other.IsNumeric()) {
    // Real can accept integer
    if (IsReal() && other.IsIntegral()) {
      return true;
    }
    
    // Integer types: check width compatibility
    if (IsIntegral() && other.IsIntegral()) {
      int this_width = GetWidth();
      int other_width = other.GetWidth();
      
      // Same width: check signedness
      if (this_width == other_width) {
        // Signed can accept unsigned with warning
        // Unsigned can accept signed with warning
        return true;
      }
      
      // Wider target can accept narrower source
      if (this_width >= other_width) {
        return true;
      }
      
      // Narrower target: truncation (with warning)
      return true;  // Allow with warning
    }
  }
  
  // 4. Logic/bit/reg are interchangeable
  if ((base_type == PrimitiveType::kLogic || 
       base_type == PrimitiveType::kBit ||
       base_type == PrimitiveType::kReg) &&
      (other.base_type == PrimitiveType::kLogic ||
       other.base_type == PrimitiveType::kBit ||
       other.base_type == PrimitiveType::kReg)) {
    // Check dimensions match
    return dimensions == other.dimensions;
  }
  
  // 5. Wire/net types
  if (IsNet() && other.IsNet()) {
    return dimensions == other.dimensions;
  }
  
  // 6. User-defined types must match exactly
  if (base_type == PrimitiveType::kUserDefined &&
      other.base_type == PrimitiveType::kUserDefined) {
    return user_type_name == other.user_type_name;
  }
  
  return false;
}

bool Type::IsNumeric() const {
  return IsIntegral() || IsReal();
}

bool Type::IsIntegral() const {
  switch (base_type) {
    case PrimitiveType::kBit:
    case PrimitiveType::kLogic:
    case PrimitiveType::kReg:
    case PrimitiveType::kInteger:
    case PrimitiveType::kInt:
    case PrimitiveType::kShortInt:
    case PrimitiveType::kLongInt:
    case PrimitiveType::kByte:
      return true;
    default:
      return false;
  }
}

bool Type::Is2State() const {
  switch (base_type) {
    case PrimitiveType::kBit:
    case PrimitiveType::kInt:
    case PrimitiveType::kShortInt:
    case PrimitiveType::kLongInt:
    case PrimitiveType::kByte:
      return true;
    default:
      return false;
  }
}

bool Type::Is4State() const {
  switch (base_type) {
    case PrimitiveType::kLogic:
    case PrimitiveType::kReg:
    case PrimitiveType::kInteger:
      return true;
    default:
      return IsNet();
  }
}

bool Type::IsReal() const {
  switch (base_type) {
    case PrimitiveType::kReal:
    case PrimitiveType::kRealTime:
    case PrimitiveType::kShortReal:
      return true;
    default:
      return false;
  }
}

bool Type::IsNet() const {
  switch (base_type) {
    case PrimitiveType::kWire:
    case PrimitiveType::kTri:
    case PrimitiveType::kSupply0:
    case PrimitiveType::kSupply1:
      return true;
    default:
      return false;
  }
}

int Type::GetWidth() const {
  if (dimensions.empty()) {
    // Default widths for types without explicit dimensions
    switch (base_type) {
      case PrimitiveType::kBit:
      case PrimitiveType::kLogic:
      case PrimitiveType::kReg:
        return 1;
      case PrimitiveType::kByte:
        return 8;
      case PrimitiveType::kShortInt:
        return 16;
      case PrimitiveType::kInt:
      case PrimitiveType::kInteger:
        return 32;
      case PrimitiveType::kLongInt:
        return 64;
      default:
        return 1;
    }
  }
  
  // Calculate total width from dimensions
  int total = 1;
  for (int dim : dimensions) {
    total *= dim;
  }
  return total;
}

bool Type::operator==(const Type& other) const {
  return base_type == other.base_type &&
         is_signed == other.is_signed &&
         is_packed == other.is_packed &&
         dimensions == other.dimensions &&
         user_type_name == other.user_type_name;
}

// Helper functions

Type MakeLogicType(int width, bool is_signed) {
  Type t(PrimitiveType::kLogic, width);
  t.is_signed = is_signed;
  return t;
}

Type MakeBitType(int width, bool is_signed) {
  Type t(PrimitiveType::kBit, width);
  t.is_signed = is_signed;
  return t;
}

Type MakeIntType() {
  return Type(PrimitiveType::kInt, 32);
}

Type MakeRealType() {
  return Type(PrimitiveType::kReal);
}

Type MakeStringType() {
  return Type(PrimitiveType::kString);
}

Type MakeUserDefinedType(const std::string& name) {
  Type t(PrimitiveType::kUserDefined);
  t.user_type_name = name;
  return t;
}

std::string PrimitiveTypeToString(PrimitiveType type) {
  switch (type) {
    case PrimitiveType::kBit: return "bit";
    case PrimitiveType::kLogic: return "logic";
    case PrimitiveType::kReg: return "reg";
    case PrimitiveType::kInteger: return "integer";
    case PrimitiveType::kInt: return "int";
    case PrimitiveType::kShortInt: return "shortint";
    case PrimitiveType::kLongInt: return "longint";
    case PrimitiveType::kByte: return "byte";
    case PrimitiveType::kReal: return "real";
    case PrimitiveType::kRealTime: return "realtime";
    case PrimitiveType::kShortReal: return "shortreal";
    case PrimitiveType::kString: return "string";
    case PrimitiveType::kChandle: return "chandle";
    case PrimitiveType::kEvent: return "event";
    case PrimitiveType::kWire: return "wire";
    case PrimitiveType::kTri: return "tri";
    case PrimitiveType::kSupply0: return "supply0";
    case PrimitiveType::kSupply1: return "supply1";
    case PrimitiveType::kVoid: return "void";
    case PrimitiveType::kUserDefined: return "<user-defined>";
    case PrimitiveType::kUnknown: return "<unknown>";
  }
  return "<invalid>";
}

}  // namespace analysis
}  // namespace verilog

