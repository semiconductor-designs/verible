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

// verilog_lexical_context.cc implements LexicalContext.

#include "verible/verilog/parser/verilog-lexical-context.h"

#include <iostream>
#include <set>
#include <stack>
#include <vector>

#include "verible/common/text/token-info.h"
#include "verible/common/util/logging.h"
#include "verible/common/util/with-reason.h"
#include "verible/verilog/parser/verilog-token-enum.h"

namespace verilog {

using verible::TokenInfo;
using verible::WithReason;

namespace internal {
// Returns true for begin/end-like tokens that can be followed with an optional
// label.
// TODO(fangism): move this to verilog_token_classifications.cc
static bool KeywordAcceptsOptionalLabel(int token_enum) {
  static const auto *keywords = new std::set<int>(
      {// begin-like keywords
       TK_begin, TK_fork, TK_generate,
       // end-like keywords
       TK_end, TK_endgenerate, TK_endcase, TK_endconfig, TK_endfunction,
       TK_endmodule, TK_endprimitive, TK_endspecify, TK_endtable, TK_endtask,
       TK_endclass, TK_endclocking, TK_endgroup, TK_endinterface, TK_endpackage,
       TK_endprogram, TK_endproperty, TK_endsequence, TK_endchecker,
       TK_endconnectrules, TK_enddiscipline, TK_endnature, TK_endparamset,
       TK_join, TK_join_any, TK_join_none});
  return keywords->find(token_enum) != keywords->end();
}

void KeywordLabelStateMachine::UpdateState(int token_enum) {
  // In any state, reset on encountering keyword.
  if (KeywordAcceptsOptionalLabel(token_enum)) {
    state_ = kGotLabelableKeyword;
    return;
  }
  // Scan for optional : label.
  switch (state_) {
    case kItemStart:
      state_ = kItemMiddle;
      break;
    case kItemMiddle:
      break;
    case kGotLabelableKeyword:
      if (token_enum == ':') {
        state_ = kGotColonExpectingLabel;
      } else {
        state_ = kItemStart;
      }
      break;
    case kGotColonExpectingLabel:
      // Expect a SymbolIdentifier as a label, but don't really care if it
      // actually is or not.
      state_ = kItemStart;
      break;
  }
}

std::ostream &ConstraintBlockStateMachine::Dump(std::ostream &os) const {
  os << '[' << states_.size() << ']';
  if (!states_.empty()) {
    os << ": top:" << int(states_.top());
  }
  return os;
}

void ConstraintBlockStateMachine::DeferInvalidToken(int token_enum) {
  // On invalid syntax, defer handling of token to previous state on the
  // stack.  If stack is empty, exit the state machine entirely.
  states_.pop();
  if (IsActive()) UpdateState(token_enum);
}

void ConstraintBlockStateMachine::UpdateState(int token_enum) {
  if (!IsActive()) {
    if (token_enum == '{') {
      // Activate this state machine.
      states_.push(kBeginningOfBlockItemOrExpression);
    }
    return;
  }
  // In verilog.y grammar:
  // see constraint_block, constraint_block_item, constraint_expression rules.
  State &top(states_.top());
  switch (top) {
    case kBeginningOfBlockItemOrExpression: {
      // Depending on the next token, push into next state, so that
      // after each list item 'pops', it returns to this state.
      switch (token_enum) {
        case TK_soft:     // fall-through
        case TK_unique:   // fall-through
        case TK_disable:  // fall-through
        case TK_solve:
          states_.push(kIgnoreUntilSemicolon);
          break;
        case TK_if:
          states_.push(kGotIf);
          break;
        case TK_else:
          states_.push(kExpectingConstraintSet);  // the else-clause
          break;
        case TK_foreach:
          states_.push(kGotForeach);
          break;
        case '(':
          states_.push(kExpectingExpressionOrImplication);
          states_.push(kInParenExpression);
          break;
        case '{':
          states_.push(kExpectingExpressionOrImplication);
          states_.push(kInBraceExpression);
          break;
        case '}':
          states_.pop();
          break;  // de-activates if this is the last level
        default:
          states_.push(kExpectingExpressionOrImplication);
      }
      break;
    }
    case kInParenExpression: {
      switch (token_enum) {
        case '(':
          states_.push(kInParenExpression);
          break;
        case ')':
          states_.pop();
          break;
        case '{':
          states_.push(kInBraceExpression);
          break;
        default:  // ignore everything else
          break;
      }
      break;
    }
    case kInBraceExpression: {
      switch (token_enum) {
        case '{':
          states_.push(kInBraceExpression);
          break;
        case '}':
          states_.pop();
          break;
        case '(':
          states_.push(kInParenExpression);
          break;
        default:  // ignore everything else
          break;
      }
      break;
    }
    case kExpectingExpressionOrImplication: {
      switch (token_enum) {
        case '{':
          states_.push(kInBraceExpression);
          break;
        case '(':
          states_.push(kInParenExpression);
          break;
        case '}':
          // Invalid in this state, but possibly valid in parent state.
          DeferInvalidToken(token_enum);
          break;
        case _TK_RARROW:             // fall-through (before interpretation)
        case TK_CONSTRAINT_IMPLIES:  // (after interpretation)
          top = kExpectingConstraintSet;  // constraint implication RHS
          break;
        case ';':
          states_.pop();
          break;
        default:  // ignore everything else
          break;
      }
      break;
    }
    case kIgnoreUntilSemicolon: {
      switch (token_enum) {
        case '(':
          states_.push(kInParenExpression);
          break;
        case '{':
          states_.push(kInBraceExpression);
          break;
        case ')':  // fall-through
        case '}':
          // Invalid syntax (unbalanced).
          DeferInvalidToken(token_enum);
          break;
        case ';':
          // Reset to expect constraint_block_item or constraint_expression.
          states_.pop();
          break;
        default:  // no change
          break;
      }
      break;
    }
    case kGotIf: {
      switch (token_enum) {
        case '(':
          // After () predicate, expect a constraint_set clause.
          top = kExpectingConstraintSet;  // the if-clause
          states_.push(kInParenExpression);
          break;
        default:
          DeferInvalidToken(token_enum);  // Invalid syntax.
      }
      break;
    }
    case kGotForeach: {
      switch (token_enum) {
        case '(':
          // After () variable list, expect a constraint_set clause.
          top = kExpectingConstraintSet;  // the foreach body
          states_.push(kInParenExpression);
          break;
        default:
          DeferInvalidToken(token_enum);  // Invalid syntax.
      }
      break;
    }
    // A constraint_set is either a {} block or a single constraint_expression.
    case kExpectingConstraintSet: {
      switch (token_enum) {
        case '{':
          // By assigning top instead of pushing, once the block is balanced,
          // it will pop back to the previous state before the construct that
          // ends with a constraint_set.
          top = kBeginningOfBlockItemOrExpression;
          break;
        default:
          // goto main handler state, which will re-write the top-of-stack.
          states_.pop();
          UpdateState(token_enum);
      }
      break;
    }
  }  // switch (top)
}

int ConstraintBlockStateMachine::InterpretToken(int token_enum) const {
  if (!IsActive() || token_enum != _TK_RARROW) return token_enum;
  // The only token re-interpreted by this state machine is "->".
  switch (states_.top()) {
    case kExpectingExpressionOrImplication:
      return TK_CONSTRAINT_IMPLIES;
    default:
      return TK_LOGICAL_IMPLIES;
  }
}

void RandomizeCallStateMachine::UpdateState(int token_enum) {
  // EBNF for randomize_call:
  // 'randomize' { attribute_instance }
  //   [ '(' [ variable_identifier_list | 'null' ] ')' ]
  //   [ 'with' [ '(' [ identifier_list ] ')' ] constraint_block ]
  switch (state_) {
    case kNone:
      if (token_enum == TK_randomize) {  // activate
        state_ = kGotRandomizeKeyword;
      }
      break;
    case kGotRandomizeKeyword:
      switch (token_enum) {
        case '(':
          state_ = kOpenedVariableList;
          break;
        case TK_with:
          state_ = kGotWithKeyword;
          break;
        default:  // anything else ends the randomize_call
          state_ = kNone;
      }
      break;
    case kOpenedVariableList:
      switch (token_enum) {
        case ')':
          state_ = kClosedVariableList;
          break;
        default:
          break;  // no state change
      }
      break;
    case kClosedVariableList:
      switch (token_enum) {
        case TK_with:
          state_ = kGotWithKeyword;
          break;
        default:  // anything else ends the randomize_call
          state_ = kNone;
      }
      break;
    case kGotWithKeyword:
      switch (token_enum) {
        case '(':
          state_ = kInsideWithIdentifierList;
          break;
        case '{':
          state_ = kInsideConstraintBlock;
          constraint_block_tracker_.UpdateState(token_enum);
          break;
        default:
          break;  // no state change
      }
      break;
    case kInsideWithIdentifierList:
      switch (token_enum) {
        case ')':
          state_ = kExpectConstraintBlock;
          break;
        default:
          break;  // no state change
      }
      break;
    case kExpectConstraintBlock:
      switch (token_enum) {
        case '{':
          state_ = kInsideConstraintBlock;
          constraint_block_tracker_.UpdateState(token_enum);
          break;
        default:  // anything else ends the randomize_call
          state_ = kNone;
          break;
      }
      break;
    case kInsideConstraintBlock: {
      constraint_block_tracker_.UpdateState(token_enum);
      if (!constraint_block_tracker_.IsActive()) {
        state_ = kNone;  // end of randomize_call
      }
      // otherwise no state change
      break;
    }
  }
}

int RandomizeCallStateMachine::InterpretToken(int token_enum) const {
  switch (state_) {
    case kInsideConstraintBlock:
      return constraint_block_tracker_.InterpretToken(token_enum);
    default:
      break;
  }
  return token_enum;  // no change
}

void ConstraintDeclarationStateMachine::UpdateState(int token_enum) {
  switch (state_) {
    case kNone:
      switch (token_enum) {
        case TK_constraint:
          state_ = kGotConstraintKeyword;
          break;
        default:
          break;  // no change
      }
      break;
    case kGotConstraintKeyword:
      switch (token_enum) {
        case SymbolIdentifier:
          state_ = kGotConstraintIdentifier;
          break;
        default:
          state_ = kNone;  // reset
      }
      break;
    case kGotConstraintIdentifier:
      switch (token_enum) {
        case '{':
          state_ = kInsideConstraintBlock;
          constraint_block_tracker_.UpdateState(token_enum);
          break;
        default:
          state_ = kNone;  // reset
      }
      break;
    case kInsideConstraintBlock:
      constraint_block_tracker_.UpdateState(token_enum);
      if (!constraint_block_tracker_.IsActive()) {
        state_ = kNone;
      }
      break;
  }
}

int ConstraintDeclarationStateMachine::InterpretToken(int token_enum) const {
  switch (state_) {
    case kInsideConstraintBlock:
      return constraint_block_tracker_.InterpretToken(token_enum);
    default:
      break;
  }
  return token_enum;  // no change
}

void LastSemicolonStateMachine::UpdateState(verible::TokenInfo *token) {
  switch (state_) {
    case kNone:
      if (token->token_enum() == trigger_token_enum_) {
        state_ = kActive;
      }  // else remain dormant
      break;
    case kActive:
      if (token->token_enum() == ';') {
        // Bookmark this token, so that it may be re-enumerated later.
        semicolons_.push(token);
      } else if (token->token_enum() == finish_token_enum_) {
        // Replace the desired ';' and return to dormant state.
        if (previous_token_ != nullptr &&
            previous_token_->token_enum() == ';') {
          // Discard the optional ';' right before the end-keyword.
          // <jedi>This is not the semicolon you are looking for.</jedi>
          semicolons_.pop();
        }
        if (!semicolons_.empty()) {
          // Re-enumerate this ';'
          semicolons_.top()->set_token_enum(semicolon_replacement_);
        }
        // Reset state machine.
        while (!semicolons_.empty()) {  // why is there no stack::clear()??
          semicolons_.pop();
        }
        state_ = kNone;
      }
      break;
  }
  previous_token_ = token;
}

}  // namespace internal

LexicalContext::LexicalContext()
    : property_declaration_tracker_(
          TK_property, TK_endproperty,
          SemicolonEndOfAssertionVariableDeclarations),
      sequence_declaration_tracker_(
          TK_sequence, TK_endsequence,
          SemicolonEndOfAssertionVariableDeclarations) {}

void LexicalContext::AdvanceToken(TokenInfo *token) {
  // Note: It might not always be possible to mutate a token as it is
  // encountered; it may have to be bookmarked to be returned to later after
  // looking ahead.

  MutateToken(token);  // only modifies token, not *this

  UpdateState(*token);  // only modifies *this, not token

  // The following state machines require a mutable token reference:
  property_declaration_tracker_.UpdateState(token);
  sequence_declaration_tracker_.UpdateState(token);

  // Maintain one token look-back.
  previous_token_ = token;
}

void LexicalContext::UpdateState(const TokenInfo &token) {
  // Forward tokens to concurrent sub-state-machines.
  {
    // Handle begin/end-like keywords with optional labels.
    keyword_label_tracker_.UpdateState(token.token_enum());

    // Parse randomize_call.
    randomize_call_tracker_.UpdateState(token.token_enum());

    // Parse constraint declarations (but not extern prototypes).
    if (!in_extern_declaration_) {
      constraint_declaration_tracker_.UpdateState(token.token_enum());
    }
  }

  // Update this state machine given current token.
  previous_token_finished_header_ = false;
  switch (token.token_enum()) {
    case '(':
      balance_stack_.push_back(&token);
      break;
    case MacroCallCloseToEndLine:  // fall-through: this is also a ')'
    case ')': {
      if (!balance_stack_.empty() &&
          balance_stack_.back()->token_enum() == '(') {
        balance_stack_.pop_back();
        // Detect ')' that exits the end of a flow-control header.
        // e.g. after "if (...)", "for (...)", "case (...)"
        if (balance_stack_.empty() && InFlowControlHeader()) {
          flow_control_stack_.back().in_body = true;
          previous_token_finished_header_ = true;
        }
      }
      break;
    }  // case ')'
    case '{':
      balance_stack_.push_back(&token);
      break;
    case '}': {
      if (!balance_stack_.empty() &&
          balance_stack_.back()->token_enum() == '{') {
        balance_stack_.pop_back();
      }
      break;
    }  // case '}'
    case TK_begin:
      block_stack_.push_back(&token);
      break;
    case TK_end: {
      if (!block_stack_.empty()) {
        block_stack_.pop_back();
        if (block_stack_.empty()) {
          // Detect the 'end' of a procedural construct statement block.
          // e.g. after "initial begin ... end"
          if (in_initial_always_final_construct_) {
            in_initial_always_final_construct_ = false;
          }
        }
      }
      break;
    }  // case TK_end
    case ';': {
      // The first ';' encountered in a function_declaration or
      // task_declaration or module_declaration marks the start of the body.
      // For extern declarations, however, there is no body that follows the
      // header, so ';' ends the declaration.
      if (in_module_declaration_) {
        if (in_extern_declaration_) {
          in_module_declaration_ = false;
          in_extern_declaration_ = false;
        } else {
          in_module_body_ = true;
        }
        previous_token_finished_header_ = true;
      }
      if (in_function_declaration_) {
        if (in_extern_declaration_) {
          in_function_declaration_ = false;
          in_extern_declaration_ = false;
        } else {
          in_function_body_ = true;
        }
        previous_token_finished_header_ = true;
      } else if (in_task_declaration_) {
        if (in_extern_declaration_) {
          in_task_declaration_ = false;
          in_extern_declaration_ = false;
        } else {
          in_task_body_ = true;
        }
        previous_token_finished_header_ = true;
      }

      if (in_initial_always_final_construct_) {
        // Exit construct for single-statement bodies.
        // e.g. initial $foo();
        seen_delay_value_in_initial_always_final_construct_context_ = false;
        if (block_stack_.empty()) {
          in_initial_always_final_construct_ = false;
        }
      }
      break;
    }  // case ';'

    // Start of flow-control block:
    case TK_if:     // fall-through
    case TK_for:    // fall-through
    case TK_case:   // fall-through
    case TK_casex:  // fall-through
    case TK_casez:
      flow_control_stack_.emplace_back(&token);
      break;

    // Procedural control blocks:
    case TK_initial:       // fall-through
    case TK_always:        // fall-through
    case TK_always_comb:   // fall-through
    case TK_always_ff:     // fall-through
    case TK_always_latch:  // fall-through
    case TK_final: {
      if (in_module_body_) {
        in_initial_always_final_construct_ = true;
      }
      break;
    }

    // Declarations (non-nestable):
    case TK_extern:
      in_extern_declaration_ = true;
      break;
    case TK_module:
      in_module_declaration_ = true;
      break;
    case TK_endmodule:
      in_module_declaration_ = false;
      in_module_body_ = false;
      break;
    case TK_function:
      in_function_declaration_ = true;
      break;
    case TK_endfunction:
      in_function_declaration_ = false;
      in_function_body_ = false;
      break;
    case TK_task:
      in_task_declaration_ = true;
      break;
    case TK_endtask:
      in_task_declaration_ = false;
      in_task_body_ = false;
      break;
    case TK_constraint:
      if (in_extern_declaration_) {
        in_extern_declaration_ = false;  // reset
      }
      break;
    case '#':
      if (in_initial_always_final_construct_) {
        seen_delay_value_in_initial_always_final_construct_context_ = true;
      }
      // std::cout << "Found delay" << std::endl;
      break;
    default:
      break;
  }  // switch (token.token_enum)
}

int LexicalContext::InterpretToken(int token_enum) const {
  // Every top-level case of this switch is a token enumeration (_TK_*)
  // that must be transformed into a disambiguated enumeration (TK_*).
  // All other tokens pass through unmodified.
  switch (token_enum) {
    // v5.6.0: Handle macro boundary markers for context preservation
    case TK_MACRO_BOUNDARY_START: {
      VLOG(2) << "==> MACRO_START (depth " << macro_depth_
              << " → " << (macro_depth_ + 1) << ")";
      
      // Save context before entering macro (non-const operation)
      // Note: This violates const-correctness but is necessary for context tracking
      // We cast away const here - this is a known limitation that will be refactored
      auto *mutable_this = const_cast<LexicalContext *>(this);
      ContextState state = SaveCurrentContext();
      mutable_this->saved_context_stack_.push(state);
      mutable_this->macro_depth_++;
      
      // Log saved state
      VLOG(2) << "    Saved: task=" << state.in_task_body
              << " function=" << state.in_function_body
              << " expecting=" << state.expecting_statement;
      
      return token_enum;  // Pass through
    }
    
    case TK_MACRO_BOUNDARY_END: {
      VLOG(2) << "==> MACRO_END (depth " << macro_depth_
              << " → " << (macro_depth_ - 1) << ")";
      
      // Restore context after exiting macro (non-const operation)
      auto *mutable_this = const_cast<LexicalContext *>(this);
      if (!saved_context_stack_.empty()) {
        ContextState state = saved_context_stack_.top();
        mutable_this->saved_context_stack_.pop();
        mutable_this->RestoreContext(state);
        
        VLOG(2) << "    Restored: task=" << in_task_body_
                << " function=" << in_function_body_;
      } else {
        LOG(WARNING) << "Context stack underflow at MACRO_END";
      }
      
      mutable_this->macro_depth_--;
      return token_enum;  // Pass through
    }

    // '->' can be interpreted as logical implication, constraint implication,
    // or event-trigger.
    case _TK_RARROW: {
      // Diagnostic logging for event trigger disambiguation
      VLOG(1) << "InterpretToken: _TK_RARROW";
      VLOG(1) << "  randomize_active=" << randomize_call_tracker_.IsActive();
      VLOG(1) << "  constraint_active=" << constraint_declaration_tracker_.IsActive();
      const bool expecting_stmt = ExpectingStatement();
      VLOG(1) << "  ExpectingStatement=" << expecting_stmt;
      VLOG(1) << "  InStatementContext=" << InStatementContext();
      VLOG(1) << "  in_task_body=" << in_task_body_;
      VLOG(1) << "  in_function_body=" << in_function_body_;
      VLOG(1) << "  in_initial_always_final=" << in_initial_always_final_construct_;
      if (previous_token_ != nullptr) {
        VLOG(1) << "  previous_token=" << previous_token_->token_enum()
                << " (text: " << previous_token_->text() << ")";
      } else {
        VLOG(1) << "  previous_token=null";
      }
      
      if (randomize_call_tracker_.IsActive()) {
        // e.g.
        //   randomize() with {
        //     x -> y;
        //   }
        VLOG(1) << "  -> Interpreted as: TK_CONSTRAINT_IMPLIES (randomize context)";
        return randomize_call_tracker_.InterpretToken(token_enum);
      }
      if (constraint_declaration_tracker_.IsActive()) {
        // e.g.
        //   constraint c {
        //     x -> y;
        //   }
        VLOG(1) << "  -> Interpreted as: TK_CONSTRAINT_IMPLIES (constraint context)";
        return constraint_declaration_tracker_.InterpretToken(token_enum);
      }
      if (expecting_stmt) {
        // e.g.
        //   task foo();
        //     ...
        //     -> x;
        //     ...
        //   endtask
        VLOG(1) << "  -> Interpreted as: TK_TRIGGER (statement context)";
        return TK_TRIGGER;
      }
      
      // BUGFIX: If in task/function body but not "expecting statement" due to
      // context loss (e.g., after macro expansion), apply a permissive rule.
      // This handles OpenTitan patterns where macros like `uvm_info(...) 
      // precede event triggers, causing ExpectingStatement() to return false
      // even though we're at statement level.
      //
      // Strategy: In task/function bodies, prefer TK_TRIGGER unless we have
      // strong evidence we're in an expression (e.g., previous token is an
      // identifier/operator that suggests binary operation).
      if ((in_task_body_ || in_function_body_) && previous_token_ != nullptr) {
        const int prev_enum = previous_token_->token_enum();
        // If previous token suggests we're in a binary expression, use IMPLIES
        // Examples: "a = b -> x" or "if (a -> b)"
        if (prev_enum == SymbolIdentifier || prev_enum == '=' ||
            prev_enum == TK_LOR || prev_enum == TK_LAND ||
            prev_enum == '(' || prev_enum == '[') {
          // Likely in an expression, keep as LOGICAL_IMPLIES
          VLOG(1) << "  -> Interpreted as: TK_LOGICAL_IMPLIES (in expression within procedural body)";
          return TK_LOGICAL_IMPLIES;
        }
        // Otherwise, in procedural body, assume TK_TRIGGER
        VLOG(1) << "  -> Interpreted as: TK_TRIGGER (permissive: in procedural body, not obviously an expression)";
        return TK_TRIGGER;
      }
      
      // Everywhere else, right-arrow should be interpreted
      // as the 'implies' binary operator for expressions.
      // e.g.
      //   if (a -> b) ...
      //   a = b -> x;
      VLOG(1) << "  -> Interpreted as: TK_LOGICAL_IMPLIES (expression context)";
      return TK_LOGICAL_IMPLIES;
    } break;
      // TODO(b/129204554): disambiguate '<='
    default:
      break;
  }
  return token_enum;
}

bool LexicalContext::InFlowControlHeader() const {
  if (flow_control_stack_.empty()) return false;
  return !flow_control_stack_.back().in_body;
}

bool LexicalContext::InAnyDeclaration() const {
  return in_function_declaration_ || in_task_declaration_ ||
         in_module_declaration_;
  // TODO(fangism): handle {interface,class} declarations
}

bool LexicalContext::InAnyDeclarationHeader() const {
  return InFunctionDeclarationHeader() || InTaskDeclarationHeader() ||
         InModuleDeclarationHeader();
  // TODO(fangism): handle {interface,class} declarations
}

bool LexicalContext::ExpectingStatement() const {
  if (InStatementContext()) {
    // Exclude states that are partially into a statement.
    const auto state = ExpectingBodyItemStart();
    VLOG(1) << __FUNCTION__ << ": InStatementContext=true, ExpectingBodyItemStart="
            << state.value << ", reason=" << state.reason;
    VLOG(2) << __FUNCTION__ << ": " << state.value << ", " << state.reason;
    return state.value;
  }
  // TODO(fangism): There are many more contexts that expect statements, add
  // them as they are needed.  In verilog.y (grammar), see statement_or_null.
  VLOG(1) << __FUNCTION__ << ": InStatementContext=false";
  return false;
}

WithReason<bool> LexicalContext::ExpectingBodyItemStart() const {
  // True when immediately entering a body section.
  // Usually false immediately after a keyword that starts a body item.
  // Usually false inside header sections of most declarations.
  // Usually false inside any () [] or {}
  // Usually true immediately after a ';' or end-like tokens.
  if (InFlowControlHeader()) return {false, "in flow control header"};
  if (InAnyDeclarationHeader()) return {false, "in other declaration header"};
  if (!balance_stack_.empty()) return {false, "balance stack not empty"};
  if (previous_token_ == nullptr) {
    // First token should be start of a description/package item.
    return {true, "first token"};
  }
  if (InAnyDeclaration() && previous_token_finished_header_) {
    return {true, "inside declaration, and reached end of header"};
  }
  switch (previous_token_->token_enum()) {
    case ';':
      return {true, "immediately following ';'"};
    // Procedural control blocks:
    case TK_initial:       // fall-through
    case TK_always:        // fall-through
    case TK_always_comb:   // fall-through
    case TK_always_ff:     // fall-through
    case TK_always_latch:  // fall-through
    case TK_final:
      return {true, "immediately following 'always/initial/final'"};
    default:
      break;
  }
  // if (InStatementContext()) {
  if (keyword_label_tracker_.ItemMayStart()) {
    return {true, "item may start"};
  }
  // return {true, "inside 'always/initial/final'"};
  // }
  if (seen_delay_value_in_initial_always_final_construct_context_) {
    return {true, "seen a delay value, expecting another statement"};
  }
  return {false, "all other cases (default)"};
}

// v5.6.0: Macro-aware context tracking helpers
LexicalContext::ContextState LexicalContext::SaveCurrentContext() const {
  ContextState state;
  state.expecting_statement = ExpectingStatement();
  state.in_task_body = in_task_body_;
  state.in_function_body = in_function_body_;
  state.in_initial_always_final_construct = in_initial_always_final_construct_;
  state.balance_depth = static_cast<int>(balance_stack_.size());
  state.previous_token = previous_token_;
  return state;
}

void LexicalContext::RestoreContext(const ContextState &state) {
  in_task_body_ = state.in_task_body;
  in_function_body_ = state.in_function_body;
  in_initial_always_final_construct_ = state.in_initial_always_final_construct;
  previous_token_ = state.previous_token;
  // Note: balance_depth is informational only, we don't restore balance_stack_
  // as it may have changed during macro expansion
}

}  // namespace verilog
