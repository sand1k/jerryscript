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
    REFERENCE, /**< Identifier or value-based reference */
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

    ret._type = jsp_operand_t::REFERENCE;
    ret._data.reference.identifier = lit_id;
    ret._is_value_based_ref = false;

    return ret;
  } /* make_identifier_operand */

  /**
   * Construct value-based reference operand with unevaluated base
   * and property name represented with a string literal
   *
   * @return constructed operand
   */
  static jsp_operand_t
  make_value_based_ref_operand_ll (lit_cpointer_t base_lit_id, /**< literal identifier
                                                                *   for reference's base */
                                   lit_cpointer_t prop_lit_id) /**< literal identifier
                                                                *   for reference's property name */
  {
    JERRY_ASSERT (base_lit_id.packed_value != NOT_A_LITERAL.packed_value);
    JERRY_ASSERT (prop_lit_id.packed_value != NOT_A_LITERAL.packed_value);

    jsp_operand_t ret;

    ret._type = jsp_operand_t::REFERENCE;
    ret._data.reference.value_based.base.lit_id = base_lit_id;
    ret._data.reference.value_based.prop_name.lit_id = prop_lit_id;
    ret._is_value_based_ref = true;
    ret._is_base_evaluated = false;
    ret._is_prop_name_value = false;

    return ret;
  } /* make_value_based_ref_operand_ll */

  /**
   * Construct value-based reference operand with evaluated base
   * and property name represented with a string literal
   *
   * @return constructed operand
   */
  static jsp_operand_t
  make_value_based_ref_operand_vl (jsp_operand_t base_value, /**< value of reference's base */
                                   lit_cpointer_t prop_lit_id) /**< literal identifier
                                                                *   for reference's property name */
  {
    JERRY_ASSERT (prop_lit_id.packed_value != NOT_A_LITERAL.packed_value);

    jsp_operand_t ret;

    JERRY_ASSERT (base_value.is_register_operand ());

    ret._type = jsp_operand_t::REFERENCE;
    ret._data.reference.value_based.base.uid = base_value.get_idx ();
    ret._data.reference.value_based.prop_name.lit_id = prop_lit_id;
    ret._is_value_based_ref = true;
    ret._is_base_evaluated = true;
    ret._is_prop_name_value = false;

    return ret;
  } /* make_value_based_ref_operand_vl */

  /**
   * Construct value-based reference operand with unevaluated base
   * and property name represented with a value
   *
   * @return constructed operand
   */
  static jsp_operand_t
  make_value_based_ref_operand_lv (lit_cpointer_t base_lit_id, /**< literal identifier
                                                                *   for reference's base */
                                   jsp_operand_t prop_name_value) /**< value of reference's property name */
  {
    jsp_operand_t ret;

    JERRY_ASSERT (base_lit_id.packed_value != NOT_A_LITERAL.packed_value);
    JERRY_ASSERT (prop_name_value.is_register_operand ());

    ret._type = jsp_operand_t::REFERENCE;
    ret._data.reference.value_based.base.lit_id = base_lit_id;
    ret._data.reference.value_based.prop_name.uid = prop_name_value.get_idx ();
    ret._is_value_based_ref = true;
    ret._is_base_evaluated = false;
    ret._is_prop_name_value = true;

    return ret;
  } /* make_value_based_ref_operand_lv */

  /**
   * Construct value-based reference operand with unevaluated base
   * and property name represented with a value
   *
   * @return constructed operand
   */
  static jsp_operand_t
  make_value_based_ref_operand_vv (jsp_operand_t base_value, /**< value of reference's base */
                                   jsp_operand_t prop_name_value) /**< value of reference's property name */
  {
    jsp_operand_t ret;

    JERRY_ASSERT (prop_name_value.is_register_operand ());

    ret._type = jsp_operand_t::REFERENCE;
    ret._data.reference.value_based.base.uid = base_value.get_idx ();
    ret._data.reference.value_based.prop_name.uid = prop_name_value.get_idx ();
    ret._is_value_based_ref = true;
    ret._is_base_evaluated = true;
    ret._is_prop_name_value = true;

    return ret;
  } /* make_value_based_ref_operand_vv */

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
   * Is it reference operand?
   *
   * @return true / false
   */
  bool is_reference_operand (void) const
  {
    JERRY_ASSERT (_type != jsp_operand_t::UNINITIALIZED);

    return (_type == jsp_operand_t::REFERENCE);
  } /* is_reference_operand */

  /**
   * Is it identifier reference operand?
   *
   * @return true / false
   */
  bool is_identifier_operand (void) const
  {
    JERRY_ASSERT (_type != jsp_operand_t::UNINITIALIZED);

    return (_type == jsp_operand_t::REFERENCE && !_is_value_based_ref);
  } /* is_identifier_operand */

  /**
   * Is it value-based reference operand?
   *
   * @return true / false
   */
  bool is_value_based_reference_operand (void) const
  {
    JERRY_ASSERT (_type != jsp_operand_t::UNINITIALIZED);

    return (_type == jsp_operand_t::REFERENCE && _is_value_based_ref);
  } /* is_value_based_reference_operand */

  /**
   * Is it evaluated value-based reference operand?
   *
   * @return true / false
   */
  bool is_evaluated_value_based_reference_operand (void) const
  {
    JERRY_ASSERT (_type == jsp_operand_t::REFERENCE && _is_value_based_ref);

    return (_is_base_evaluated);
  } /* is_evaluated_value_based_reference_operand */

  /**
   * Get string literal - name of Identifier reference
   *
   * @return literal identifier
   */
  lit_cpointer_t get_identifier_name (void) const
  {
    JERRY_ASSERT (_type == jsp_operand_t::REFERENCE && !_is_value_based_ref);

    return (_data.reference.identifier);
  } /* get_identifier_name */

  /**
   * Get Identifier name - non-evaluated base of a value-based reference
   *
   * @return identifier reference operand
   */
  jsp_operand_t get_value_based_ref_base_identifier (void) const
  {
    JERRY_ASSERT (_type == jsp_operand_t::REFERENCE
                  && _is_value_based_ref
                  && !_is_base_evaluated);

    return jsp_operand_t::make_identifier_operand (_data.reference.value_based.base.lit_id);
  } /* get_value_based_ref_base_identifier */

  /**
   * Get evaluated base of a value-based reference
   *
   * @return register operand
   */
  jsp_operand_t get_value_based_ref_base_value (void) const
  {
    JERRY_ASSERT (_type == jsp_operand_t::REFERENCE
                  && _is_value_based_ref
                  && _is_base_evaluated);

    return jsp_operand_t::make_reg_operand (_data.reference.value_based.base.uid);
  } /* get_value_based_ref_base_value */

  /**
   * Get base of a value-based reference
   *
   * @return operand
   */
  jsp_operand_t get_value_based_ref_base (void) const
  {
    JERRY_ASSERT (_type == jsp_operand_t::REFERENCE && _is_value_based_ref);

    if (_is_base_evaluated)
    {
      return get_value_based_ref_base_value ();
    }
    else
    {
      return get_value_based_ref_base_identifier ();
    }
  } /* get_value_based_ref_base */

  /**
   * Get property name of a value-based reference
   *
   * @return register / literal operand
   */
  jsp_operand_t get_value_based_ref_prop_name (void) const
  {
    JERRY_ASSERT (_type == jsp_operand_t::REFERENCE && _is_value_based_ref);

    if (_is_prop_name_value)
    {
      return jsp_operand_t::make_reg_operand (_data.reference.value_based.prop_name.uid);
    }
    else
    {
      return jsp_operand_t::make_lit_operand (_data.reference.value_based.prop_name.lit_id);
    }
  } /* get_value_based_ref_prop_name */

  /**
   * Get property name value of a value-based reference
   *
   * @return register operand
   */
  jsp_operand_t get_value_based_ref_prop_name_value (void) const
  {
    JERRY_ASSERT (_type == jsp_operand_t::REFERENCE
                  && _is_value_based_ref
                  && _is_prop_name_value);

    return jsp_operand_t::make_reg_operand (_data.reference.value_based.prop_name.uid);
  } /* get_value_based_ref_prop_name_value */

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

    /**
     * Reference (jsp_operand_t::REFERENCE)
     */
    union
    {
      /**
       * Value-based reference (is_value_based_ref flag set)
       */
      struct
      {
        typedef union
        {
          vm_idx_t uid; /**< index of register with value */
          lit_cpointer_t lit_id; /**< literal identifier - name of identifier that could be evaluated to a value */
        } ref_part_descr_t;

        ref_part_descr_t base; /**< base of reference */
        ref_part_descr_t prop_name; /**< property name of reference */
      } value_based;

      /**
       * Identifier reference (is_value_based_ref flag not set)
       */
      lit_cpointer_t identifier;
    } reference; /**< reference descriptor */
  } _data;

  type_t _type; /**< type of operand */

  /*
   * Reference-related flags (only valid if reference's type is jsp_operand_t::REFERENCE)
   *
   * The flags are stored separately from corresponding reference
   * description parts to reduce size of jsp_operand_t structure
   * while avoiding __attr_packed___ usage.
   */
  uint8_t _is_value_based_ref : 1; /**< is reference, described by the operand, value-based (flag set)
                                    *   or a simple Identifier reference (flag not set) */
  uint8_t _is_base_evaluated : 1; /**< if is_value_based_ref is set, this flag indicates whether the base part of
                                   *   reference is represented as a literal (i.e. not evaluated yet - flag not set),
                                   *   or as an already evaluated part of reference - i.e. as a register with value
                                   *   (flag set) */
  uint8_t _is_prop_name_value : 1; /**< if is_value_based_ref is set, this flag indicates whether the property name
                                    *   part of reference is represented with a string literal (flag not set),
                                    *   or as a value - i.e. as a register with value (flag set) */
};

static_assert (sizeof (jsp_operand_t) == 6, "");

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
jsp_operand_t eval_ret_operand (void);
jsp_operand_t jsp_create_operand_for_in_special_reg (void);
jsp_operand_t tmp_operand (void);
bool operand_is_empty (jsp_operand_t);

void dumper_init (void);
void dumper_free (void);

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

jsp_operand_t dump_array_hole_assignment_res (void);
void dump_boolean_assignment (jsp_operand_t, bool);
void dump_string_assignment (jsp_operand_t, lit_cpointer_t);
void dump_number_assignment (jsp_operand_t, lit_cpointer_t);
void dump_regexp_assignment (jsp_operand_t, lit_cpointer_t);
void dump_smallint_assignment (jsp_operand_t, vm_idx_t);
void dump_undefined_assignment (jsp_operand_t);
jsp_operand_t dump_undefined_assignment_res (void);
void dump_null_assignment (jsp_operand_t);
void dump_variable_assignment (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_variable_assignment_res (jsp_operand_t);

vm_instr_counter_t dump_varg_header_for_rewrite (varg_list_type, jsp_operand_t);
jsp_operand_t rewrite_varg_header_set_args_count (size_t, vm_instr_counter_t);
void dump_call_additional_info (opcode_call_flags_t, jsp_operand_t);
void dump_varg (jsp_operand_t);

void dump_prop_name_and_value (jsp_operand_t, jsp_operand_t);
void dump_prop_getter_decl (jsp_operand_t, jsp_operand_t);
void dump_prop_setter_decl (jsp_operand_t, jsp_operand_t);
void dump_prop_getter (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_prop_getter_res (jsp_operand_t);
void dump_prop_setter (jsp_operand_t, jsp_operand_t);

void dump_function_end_for_rewrite (void);
void rewrite_function_end (vm_instr_counter_t);

jsp_operand_t dump_this_res (void);

void dump_post_increment (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_post_increment_res (jsp_operand_t);
void dump_post_decrement (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_post_decrement_res (jsp_operand_t);
void dump_pre_increment (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_pre_increment_res (jsp_operand_t);
void dump_pre_decrement (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_pre_decrement_res (jsp_operand_t);
void dump_unary_plus (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_unary_plus_res (jsp_operand_t);
void dump_unary_minus (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_unary_minus_res (jsp_operand_t);
void dump_bitwise_not (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_bitwise_not_res (jsp_operand_t);
void dump_logical_not (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_logical_not_res (jsp_operand_t);

void dump_multiplication (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_multiplication_res (jsp_operand_t, jsp_operand_t);
void dump_division (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_division_res (jsp_operand_t, jsp_operand_t);
void dump_remainder (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_remainder_res (jsp_operand_t, jsp_operand_t);
void dump_addition (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_addition_res (jsp_operand_t, jsp_operand_t);
void dump_substraction (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_substraction_res (jsp_operand_t, jsp_operand_t);
void dump_left_shift (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_left_shift_res (jsp_operand_t, jsp_operand_t);
void dump_right_shift (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_right_shift_res (jsp_operand_t, jsp_operand_t);
void dump_right_shift_ex (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_right_shift_ex_res (jsp_operand_t, jsp_operand_t);
void dump_less_than (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_less_than_res (jsp_operand_t, jsp_operand_t);
void dump_greater_than (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_greater_than_res (jsp_operand_t, jsp_operand_t);
void dump_less_or_equal_than (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_less_or_equal_than_res (jsp_operand_t, jsp_operand_t);
void dump_greater_or_equal_than (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_greater_or_equal_than_res (jsp_operand_t, jsp_operand_t);
void dump_instanceof (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_instanceof_res (jsp_operand_t, jsp_operand_t);
void dump_in (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_in_res (jsp_operand_t, jsp_operand_t);
void dump_equal_value (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_equal_value_res (jsp_operand_t, jsp_operand_t);
void dump_not_equal_value (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_not_equal_value_res (jsp_operand_t, jsp_operand_t);
void dump_equal_value_type (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_equal_value_type_res (jsp_operand_t, jsp_operand_t);
void dump_not_equal_value_type (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_not_equal_value_type_res (jsp_operand_t, jsp_operand_t);
void dump_bitwise_and (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_bitwise_and_res (jsp_operand_t, jsp_operand_t);
void dump_bitwise_xor (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_bitwise_xor_res (jsp_operand_t, jsp_operand_t);
void dump_bitwise_or (jsp_operand_t, jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_bitwise_or_res (jsp_operand_t, jsp_operand_t);

vm_instr_counter_t dump_conditional_check_for_rewrite (jsp_operand_t);
void rewrite_conditional_check (vm_instr_counter_t);
vm_instr_counter_t dump_jump_to_end_for_rewrite (void);
void rewrite_jump_to_end (vm_instr_counter_t);

jsp_operand_t dump_prop_setter_or_variable_assignment_res (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_prop_setter_or_addition_res (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_prop_setter_or_multiplication_res (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_prop_setter_or_division_res (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_prop_setter_or_remainder_res (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_prop_setter_or_substraction_res (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_prop_setter_or_left_shift_res (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_prop_setter_or_right_shift_res (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_prop_setter_or_right_shift_ex_res (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_prop_setter_or_bitwise_and_res (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_prop_setter_or_bitwise_xor_res (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_prop_setter_or_bitwise_or_res (jsp_operand_t, jsp_operand_t);

void dumper_set_break_target (void);
void dumper_set_continue_target (void);
vm_instr_counter_t dumper_set_next_iteration_target (void);
vm_instr_counter_t
dump_simple_or_nested_jump_for_rewrite (vm_op_t, jsp_operand_t, vm_instr_counter_t);
vm_instr_counter_t
rewrite_simple_or_nested_jump_and_get_next (vm_instr_counter_t, vm_instr_counter_t);
void dump_continue_iterations_check (vm_instr_counter_t, jsp_operand_t);

void start_dumping_case_clauses (void);
vm_instr_counter_t dump_case_clause_check_for_rewrite (jsp_operand_t, jsp_operand_t);
vm_instr_counter_t dump_default_clause_check_for_rewrite (void);
void rewrite_case_clause (vm_instr_counter_t);
void rewrite_default_clause (vm_instr_counter_t);
void finish_dumping_case_clauses (void);

void dump_delete (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_delete_res (jsp_operand_t);

void dump_typeof (jsp_operand_t, jsp_operand_t);
jsp_operand_t dump_typeof_res (jsp_operand_t);

vm_instr_counter_t dump_with_for_rewrite (jsp_operand_t);
void rewrite_with (vm_instr_counter_t);
void dump_with_end (void);

vm_instr_counter_t dump_for_in_for_rewrite (jsp_operand_t);
void rewrite_for_in (vm_instr_counter_t);
void dump_for_in_end (void);

vm_instr_counter_t dump_try_for_rewrite (void);
vm_instr_counter_t dump_catch_for_rewrite (jsp_operand_t);
vm_instr_counter_t dump_finally_for_rewrite (void);
void rewrite_try (vm_instr_counter_t);
void rewrite_catch (vm_instr_counter_t);
void rewrite_finally (vm_instr_counter_t);
void dump_end_try_catch_finally (void);
void dump_throw (jsp_operand_t);

void dump_variable_declaration (lit_cpointer_t);

vm_instr_counter_t dump_scope_code_flags_for_rewrite (void);
void rewrite_scope_code_flags (vm_instr_counter_t, opcode_scope_code_flags_t);

vm_instr_counter_t dump_reg_var_decl_for_rewrite (void);
void rewrite_reg_var_decl (vm_instr_counter_t);

void dump_ret (void);
void dump_retval (jsp_operand_t);

#endif /* OPCODES_DUMPER_H */
