/* Copyright 2014-2015 Samsung Electronics Co., Ltd.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef OPCODES_DUMPER_H
#define OPCODES_DUMPER_H

#include "ecma-globals.h"
#include "lexer.h"
#include "opcodes.h"
#include "scopes-tree.h"
#include "serializer.h"

/**
 * Operand (descriptor of value or reference in context of parser)
 */
class jsp_operand_t
{
public:
  enum type_t : uint8_t
  {
    EMPTY, /**< empty operand */
    LITERAL, /**< operand contains literal value */
    IDENTIFIER, /**< Identifier reference */
    TMP, /**< operand contains byte-code register index */
    IDX_CONST, /**< operand contains an integer constant that fits vm_idx_t */
    UNKNOWN, /**< operand, representing unknown value that would be rewritten later */
    UNINITIALIZED /**< uninitialized operand
                   *
                   *   Note:
                   *      For use only in assertions to check that operands
                   *      are initialized before actual usage */
  };

  /**
   * Construct operand template
   */
  jsp_operand_t (void)
  {
#ifndef JERRY_NDEBUG
    _type = jsp_operand_t::UNINITIALIZED;
#endif /* !JERRY_NDEBUG */
  } /* jsp_operand_t */

  /**
   * Construct empty operand
   *
   * @return constructed operand
   */
  static jsp_operand_t
  make_empty_operand (void)
  {
    jsp_operand_t ret;

    ret._type = jsp_operand_t::EMPTY;

    return ret;
  } /* make_empty_operand */

  /**
   * Construct unknown operand
   *
   * @return constructed operand
   */
  static jsp_operand_t
  make_unknown_operand (void)
  {
    jsp_operand_t ret;

    ret._type = jsp_operand_t::UNKNOWN;

    return ret;
  } /* make_unknown_operand */

  /**
   * Construct idx-constant operand
   *
   * @return constructed operand
   */
  static jsp_operand_t
  make_idx_const_operand (vm_idx_t cnst) /**< integer in vm_idx_t range */
  {
    jsp_operand_t ret;

    ret._type = jsp_operand_t::IDX_CONST;
    ret._data.idx_const = cnst;

    return ret;
  } /* make_idx_const_operand */

  /**
   * Construct literal operand
   *
   * @return constructed operand
   */
  static jsp_operand_t
  make_lit_operand (lit_cpointer_t lit_id) /**< literal identifier */
  {
    JERRY_ASSERT (lit_id.packed_value != NOT_A_LITERAL.packed_value);

    jsp_operand_t ret;

    ret._type = jsp_operand_t::LITERAL;
    ret._data.lit_id = lit_id;

    return ret;
  } /* make_lit_operand */

  /**
   * Construct identifier reference operand
   *
   * @return constructed operand
   */
  static jsp_operand_t
  make_identifier_operand (lit_cpointer_t lit_id) /**< literal identifier */
  {
    JERRY_ASSERT (lit_id.packed_value != NOT_A_LITERAL.packed_value);

    jsp_operand_t ret;

    ret._type = jsp_operand_t::IDENTIFIER;
    ret._data.identifier = lit_id;

    return ret;
  } /* make_identifier_operand */

  /**
   * Construct register operand
   *
   * @return constructed operand
   */
  static jsp_operand_t
  make_reg_operand (vm_idx_t reg_index) /**< register index */
  {
    /*
     * The following check currently leads to 'comparison is always true
     * due to limited range of data type' warning, so it is turned off.
     *
     * If VM_IDX_GENERAL_VALUE_FIRST is changed to value greater than 0,
     * the check should be restored.
     */
    // JERRY_ASSERT (reg_index >= VM_IDX_GENERAL_VALUE_FIRST);
    static_assert (VM_IDX_GENERAL_VALUE_FIRST == 0, "See comment above");

    JERRY_ASSERT (reg_index <= VM_IDX_GENERAL_VALUE_LAST);

    jsp_operand_t ret;

    ret._type = jsp_operand_t::TMP;
    ret._data.uid = reg_index;

    return ret;
  } /* make_reg_operand */

  /**
   * Is it empty operand?
   *
   * @return true / false
   */
  bool
  is_empty_operand (void) const
  {
    JERRY_ASSERT (_type != jsp_operand_t::UNINITIALIZED);

    return (_type == jsp_operand_t::EMPTY);
  } /* is_empty_operand */

  /**
   * Is it unknown operand?
   *
   * @return true / false
   */
  bool
  is_unknown_operand (void) const
  {
    JERRY_ASSERT (_type != jsp_operand_t::UNINITIALIZED);

    return (_type == jsp_operand_t::UNKNOWN);
  } /* is_unknown_operand */

  /**
   * Is it idx-constant operand?
   *
   * @return true / false
   */
  bool
  is_idx_const_operand (void) const
  {
    JERRY_ASSERT (_type != jsp_operand_t::UNINITIALIZED);

    return (_type == jsp_operand_t::IDX_CONST);
  } /* is_idx_const_operand */

  /**
   * Is it byte-code register operand?
   *
   * @return true / false
   */
  bool
  is_register_operand (void) const
  {
    JERRY_ASSERT (_type != jsp_operand_t::UNINITIALIZED);

    return (_type == jsp_operand_t::TMP);
  } /* is_register_operand */

  /**
   * Is it literal operand?
   *
   * @return true / false
   */
  bool
  is_literal_operand (void) const
  {
    JERRY_ASSERT (_type != jsp_operand_t::UNINITIALIZED);

    return (_type == jsp_operand_t::LITERAL);
  } /* is_literal_operand */

  /**
   * Is it identifier reference operand?
   *
   * @return true / false
   */
  bool is_identifier_operand (void) const
  {
    JERRY_ASSERT (_type != jsp_operand_t::UNINITIALIZED);

    return (_type == jsp_operand_t::IDENTIFIER);
  } /* is_identifier_operand */

  /**
   * Get string literal - name of Identifier reference
   *
   * @return literal identifier
   */
  lit_cpointer_t get_identifier_name (void) const
  {
    JERRY_ASSERT (is_identifier_operand ());

    return (_data.identifier);
  } /* get_identifier_name */

  /**
   * Get idx for operand
   *
   * @return VM_IDX_REWRITE_LITERAL_UID (for jsp_operand_t::LITERAL),
   *         or register index (for jsp_operand_t::TMP).
   */
  vm_idx_t
  get_idx (void) const
  {
    JERRY_ASSERT (_type != jsp_operand_t::UNINITIALIZED);

    if (_type == jsp_operand_t::TMP)
    {
      return _data.uid;
    }
    else if (_type == jsp_operand_t::LITERAL)
    {
      return VM_IDX_REWRITE_LITERAL_UID;
    }
    else
    {
      JERRY_ASSERT (_type == jsp_operand_t::EMPTY);

      return VM_IDX_EMPTY;
    }
  } /* get_idx */

  /**
   * Get literal from operand
   *
   * @return literal identifier (for jsp_operand_t::LITERAL),
   *         or NOT_A_LITERAL (for jsp_operand_t::TMP).
   */
  lit_cpointer_t
  get_literal (void) const
  {
    JERRY_ASSERT (_type != jsp_operand_t::UNINITIALIZED);

    if (_type == jsp_operand_t::TMP)
    {
      return NOT_A_LITERAL;
    }
    else if (_type == jsp_operand_t::LITERAL)
    {
      return _data.lit_id;
    }
    else
    {
      JERRY_ASSERT (_type == jsp_operand_t::EMPTY);

      return NOT_A_LITERAL;
    }
  } /* get_literal */

  /**
   * Get constant from idx-constant operand
   *
   * @return an integer
   */
  vm_idx_t
  get_idx_const (void) const
  {
    JERRY_ASSERT (is_idx_const_operand ());

    return _data.idx_const;
  } /* get_idx_const */

private:
  union
  {
    vm_idx_t idx_const; /**< idx constant value (for jsp_operand_t::IDX_CONST) */
    vm_idx_t uid; /**< register index (for jsp_operand_t::TMP) */
    lit_cpointer_t lit_id; /**< literal (for jsp_operand_t::LITERAL) */
    lit_cpointer_t identifier; /**< Identifier reference (is_value_based_ref flag not set) */
  } _data;

  type_t _type; /**< type of operand */
};

static_assert (sizeof (jsp_operand_t) == 4, "");

typedef enum __attr_packed___
{
  VARG_FUNC_DECL,
  VARG_FUNC_EXPR,
  VARG_ARRAY_DECL,
  VARG_OBJ_DECL,
  VARG_CONSTRUCT_EXPR,
  VARG_CALL_EXPR
} varg_list_type;

jsp_operand_t empty_operand (void);
jsp_operand_t literal_operand (lit_cpointer_t);
jsp_operand_t tmp_operand (void);
bool operand_is_empty (jsp_operand_t);

void dumper_init (bool);
void dumper_free (void);

void dumper_rewrite_op_meta (scopes_tree, vm_instr_counter_t, op_meta);

void dumper_start_move_of_vars_to_regs ();
bool dumper_start_move_of_args_to_regs (uint32_t args_num);
bool dumper_try_replace_identifier_name_with_reg (scopes_tree, op_meta *);
void dumper_alloc_reg_for_unused_arg (void);

void dumper_new_statement (void);
void dumper_new_scope (vm_idx_t *, vm_idx_t *);
void dumper_finish_scope (vm_idx_t, vm_idx_t);
vm_idx_t dumper_start_varg_code_sequence (void);
void dumper_finish_varg_code_sequence (vm_idx_t);

extern bool dumper_is_eval_literal (jsp_operand_t);

void dump_array_hole_assignment (jsp_operand_t);
void dump_boolean_assignment (jsp_operand_t, bool);
void dump_string_assignment (jsp_operand_t, lit_cpointer_t);
void dump_number_assignment (jsp_operand_t, lit_cpointer_t);
void dump_regexp_assignment (jsp_operand_t, lit_cpointer_t);
void dump_smallint_assignment (jsp_operand_t, vm_idx_t);
void dump_undefined_assignment (jsp_operand_t);
void dump_null_assignment (jsp_operand_t);
void dump_variable_assignment (jsp_operand_t, jsp_operand_t);

vm_instr_counter_t dump_varg_header_for_rewrite (varg_list_type, jsp_operand_t);
void rewrite_varg_header_set_args_count (scopes_tree, jsp_operand_t, size_t, vm_instr_counter_t);
void dump_call_additional_info (opcode_call_flags_t, jsp_operand_t);
void dump_varg (jsp_operand_t);

void dump_prop_name_and_value (jsp_operand_t, jsp_operand_t);
void dump_prop_getter_decl (jsp_operand_t, jsp_operand_t);
void dump_prop_setter_decl (jsp_operand_t, jsp_operand_t);
void dump_prop_getter (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_prop_setter (jsp_operand_t, jsp_operand_t, jsp_operand_t);

void dump_function_end_for_rewrite (void);
void rewrite_function_end (scopes_tree, vm_instr_counter_t);

void dump_unary_plus (jsp_operand_t, jsp_operand_t);
void dump_unary_minus (jsp_operand_t, jsp_operand_t);
void dump_bitwise_not (jsp_operand_t, jsp_operand_t);
void dump_logical_not (jsp_operand_t, jsp_operand_t);

void dump_multiplication (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_division (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_remainder (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_addition (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_substraction (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_left_shift (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_right_shift (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_right_shift_ex (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_less_than (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_greater_than (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_less_or_equal_than (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_greater_or_equal_than (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_instanceof (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_in (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_equal_value (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_not_equal_value (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_equal_value_type (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_not_equal_value_type (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_bitwise_and (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_bitwise_xor (jsp_operand_t, jsp_operand_t, jsp_operand_t);
void dump_bitwise_or (jsp_operand_t, jsp_operand_t, jsp_operand_t);

vm_instr_counter_t dump_conditional_check_for_rewrite (jsp_operand_t);
void rewrite_conditional_check (scopes_tree, vm_instr_counter_t);
vm_instr_counter_t dump_jump_to_end_for_rewrite (void);
void rewrite_jump_to_end (scopes_tree, vm_instr_counter_t);

vm_instr_counter_t dumper_set_next_iteration_target (void);
vm_instr_counter_t dump_simple_or_nested_jump_for_rewrite (vm_op_t, jsp_operand_t, vm_instr_counter_t);
vm_instr_counter_t rewrite_simple_or_nested_jump_and_get_next (scopes_tree, vm_instr_counter_t, vm_instr_counter_t);
void dump_continue_iterations_check (vm_instr_counter_t, jsp_operand_t);

void start_dumping_case_clauses (void);
vm_instr_counter_t dump_case_clause_check_for_rewrite (jsp_operand_t);
vm_instr_counter_t dump_default_clause_check_for_rewrite (void);
void rewrite_case_clause (scopes_tree, vm_instr_counter_t);
void rewrite_default_clause (scopes_tree, vm_instr_counter_t);
void finish_dumping_case_clauses (void);

void dump_delete (jsp_operand_t, jsp_operand_t);
void dump_delete_prop (jsp_operand_t, jsp_operand_t, jsp_operand_t);

void dump_typeof (jsp_operand_t, jsp_operand_t);

void dump_unary_op (vm_op_t, jsp_operand_t, jsp_operand_t);
void dump_binary_op (vm_op_t, jsp_operand_t, jsp_operand_t, jsp_operand_t);

vm_instr_counter_t dump_with_for_rewrite (jsp_operand_t);
void rewrite_with (scopes_tree, vm_instr_counter_t);
void dump_with_end (void);

vm_instr_counter_t dump_for_in_for_rewrite (jsp_operand_t);
void rewrite_for_in (scopes_tree, vm_instr_counter_t);
void dump_for_in_end (void);

vm_instr_counter_t dump_try_for_rewrite (void);
vm_instr_counter_t dump_catch_for_rewrite (jsp_operand_t);
vm_instr_counter_t dump_finally_for_rewrite (void);
void rewrite_try (scopes_tree, vm_instr_counter_t);
void rewrite_catch (scopes_tree, vm_instr_counter_t);
void rewrite_finally (scopes_tree, vm_instr_counter_t);
void dump_end_try_catch_finally (void);
void dump_throw (jsp_operand_t);

void dump_variable_declaration (lit_cpointer_t);

vm_instr_counter_t dump_scope_code_flags_for_rewrite (void);
void rewrite_scope_code_flags (scopes_tree, vm_instr_counter_t, opcode_scope_code_flags_t);

vm_instr_counter_t dump_reg_var_decl_for_rewrite (void);
void rewrite_reg_var_decl (scopes_tree, vm_instr_counter_t);

void dump_ret (void);
void dump_retval (jsp_operand_t);

#endif /* OPCODES_DUMPER_H */
