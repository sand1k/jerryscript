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

#include "jsp-early-error.h"
#include "opcodes-dumper.h"
#include "pretty-printer.h"
#include "bytecode-data.h"

/**
 * Register allocator's counter
 */
static vm_idx_t jsp_reg_next;

/**
 * Maximum identifier of a register, allocated for intermediate value storage
 *
 * See also:
 *          dumper_save_reg_alloc_ctx, dumper_restore_reg_alloc_ctx
 */
static vm_idx_t jsp_reg_max_for_temps;

/**
 * Maximum identifier of a register, allocated for storage of a variable value.
 *
 * The value can be VM_IDX_EMPTY, indicating that no registers were allocated for variable values.
 *
 * Note:
 *      Registers for variable values are always allocated after registers for temporary values,
 *      so the value, if not equal to VM_IDX_EMPTY, is always greater than jsp_reg_max_for_temps.
 *
 * See also:
 *          dumper_try_replace_identifier_name_with_reg
 */
static vm_idx_t jsp_reg_max_for_local_var;

/**
 * Maximum identifier of a register, allocated for storage of an argument value.
 *
 * The value can be VM_IDX_EMPTY, indicating that no registers were allocated for argument values.
 *
 * Note:
 *      Registers for argument values are always allocated after registers for variable values,
 *      so the value, if not equal to VM_IDX_EMPTY, is always greater than jsp_reg_max_for_local_var.
 *
 * See also:
 *          dumper_try_replace_identifier_name_with_reg
 */
static vm_idx_t jsp_reg_max_for_args;

bool is_print_instrs = false;
scopes_tree current_scope_p = NULL;
/**
 * Flag, indicating if bytecode should be generated
 */
bool is_generate_bytecode = false;

/**
 * Temporary literal set is used for estimation of number of unique literals
 * in a byte-code instructions block (BLOCK_SIZE). The calculated number
 * is always equal or larger than actual number of unique literals.
 *
 * The set is emptied upon:
 *  - reaching a bytecode block border;
 *  - changing scope, to which instructions are dumped.
 *
 * Emptying the set in second case is necessary, as the set should contain
 * unique literals of a bytecode block, and, upon switching to another scope,
 * current bytecode block is also switched, correspondingly. However, this
 * could only lead to overestimation of unique literals number, relatively
 * to the actual number.
 */

/**
 * Size of the temporary literal set
 */
#define SCOPE_TMP_LIT_SET_SIZE 32
/**
 * Container of the temporary literal set
 */
static lit_cpointer_t scopes_tmp_lit_set [SCOPE_TMP_LIT_SET_SIZE];

/**
 * Number of items in the temporary literal set
 */
static uint8_t scopes_tmp_lit_set_num;

/**
 * Scope that is associated with the temporary literal set
 */
static scopes_tree scopes_tmp_lit_set_scope_p = NULL;

static bool
is_possible_literal (uint16_t mask, uint8_t index)
{
  int res;
  switch (index)
  {
    case 0:
    {
      res = mask >> 8;
      break;
    }
    case 1:
    {
      res = (mask & 0xF0) >> 4;
      break;
    }
    default:
    {
      JERRY_ASSERT (index = 2);
      res = mask & 0x0F;
    }
  }
  JERRY_ASSERT (res == 0 || res == 1);
  return res == 1;
}

static vm_idx_t
get_uid (op_meta *op, size_t i)
{
  JERRY_ASSERT (i < 3);
  return op->op.data.raw_args[i];
}

static void
insert_uids_to_lit_id_map (scopes_tree scope_p, op_meta *om, uint16_t mask)
{
  for (uint8_t i = 0; i < 3; i++)
  {
    if (is_possible_literal (mask, i))
    {
      if (get_uid (om, i) == VM_IDX_REWRITE_LITERAL_UID)
      {
        JERRY_ASSERT (om->lit_id[i].packed_value != MEM_CP_NULL);
        lit_cpointer_t lit_id = om->lit_id[i];

        JERRY_ASSERT (scopes_tmp_lit_set_scope_p == scope_p);

        uint8_t tmp_hash_table_index;
        for (tmp_hash_table_index = 0;
             tmp_hash_table_index < scopes_tmp_lit_set_num;
             tmp_hash_table_index++)
        {
          if (scopes_tmp_lit_set [tmp_hash_table_index].packed_value == lit_id.packed_value)
          {
            break;
          }
        }

        if (tmp_hash_table_index == scopes_tmp_lit_set_num)
        {
          scope_p->max_uniq_literals_num++;

          if (scopes_tmp_lit_set_num < SCOPE_TMP_LIT_SET_SIZE)
          {
            scopes_tmp_lit_set [scopes_tmp_lit_set_num ++] = lit_id;
          }
          else
          {
            JERRY_ASSERT (scopes_tmp_lit_set_num != 0);

            scopes_tmp_lit_set [scopes_tmp_lit_set_num - 1u] = lit_id;
          }
        }
      }
      else
      {
        JERRY_ASSERT (om->lit_id[i].packed_value == MEM_CP_NULL);
      }
    }
    else
    {
      JERRY_ASSERT (om->lit_id[i].packed_value == MEM_CP_NULL);
    }
  }
}

/**
 * Count number of literals in instruction which were not seen previously
 */
static void
count_new_literals_in_instr (scopes_tree scope_p,
                             vm_instr_counter_t instr_pos, /**< position of instruction */
                             op_meta *om_p) /**< instruction */
{
  if (scope_p != scopes_tmp_lit_set_scope_p)
  {
    scopes_tmp_lit_set_scope_p = scope_p;
    scopes_tmp_lit_set_num = 0;
  }

  if (instr_pos % BLOCK_SIZE == 0)
  {
    scopes_tmp_lit_set_num = 0;
  }

  switch (om_p->op.op_idx)
  {
    case VM_OP_PROP_GETTER:
    case VM_OP_PROP_SETTER:
    case VM_OP_DELETE_PROP:
    case VM_OP_B_SHIFT_LEFT:
    case VM_OP_B_SHIFT_RIGHT:
    case VM_OP_B_SHIFT_URIGHT:
    case VM_OP_B_AND:
    case VM_OP_B_OR:
    case VM_OP_B_XOR:
    case VM_OP_EQUAL_VALUE:
    case VM_OP_NOT_EQUAL_VALUE:
    case VM_OP_EQUAL_VALUE_TYPE:
    case VM_OP_NOT_EQUAL_VALUE_TYPE:
    case VM_OP_LESS_THAN:
    case VM_OP_GREATER_THAN:
    case VM_OP_LESS_OR_EQUAL_THAN:
    case VM_OP_GREATER_OR_EQUAL_THAN:
    case VM_OP_INSTANCEOF:
    case VM_OP_IN:
    case VM_OP_ADDITION:
    case VM_OP_SUBSTRACTION:
    case VM_OP_DIVISION:
    case VM_OP_MULTIPLICATION:
    case VM_OP_REMAINDER:
    {
      insert_uids_to_lit_id_map (scope_p, om_p, 0x111);
      break;
    }
    case VM_OP_CALL_N:
    case VM_OP_CONSTRUCT_N:
    case VM_OP_FUNC_EXPR_N:
    case VM_OP_DELETE_VAR:
    case VM_OP_TYPEOF:
    case VM_OP_B_NOT:
    case VM_OP_LOGICAL_NOT:
    case VM_OP_POST_INCR:
    case VM_OP_POST_DECR:
    case VM_OP_PRE_INCR:
    case VM_OP_PRE_DECR:
    case VM_OP_UNARY_PLUS:
    case VM_OP_UNARY_MINUS:
    {
      insert_uids_to_lit_id_map (scope_p, om_p, 0x110);
      break;
    }
    case VM_OP_ASSIGNMENT:
    {
      switch (om_p->op.data.assignment.type_value_right)
      {
        case OPCODE_ARG_TYPE_SIMPLE:
        case OPCODE_ARG_TYPE_SMALLINT:
        case OPCODE_ARG_TYPE_SMALLINT_NEGATE:
        {
          insert_uids_to_lit_id_map (scope_p, om_p, 0x100);
          break;
        }
        case OPCODE_ARG_TYPE_NUMBER:
        case OPCODE_ARG_TYPE_NUMBER_NEGATE:
        case OPCODE_ARG_TYPE_REGEXP:
        case OPCODE_ARG_TYPE_STRING:
        case OPCODE_ARG_TYPE_VARIABLE:
        {
          insert_uids_to_lit_id_map (scope_p, om_p, 0x101);
          break;
        }
      }
      break;
    }
    case VM_OP_FUNC_DECL_N:
    case VM_OP_FUNC_EXPR_REF:
    case VM_OP_FOR_IN:
    case VM_OP_ARRAY_DECL:
    case VM_OP_OBJ_DECL:
    case VM_OP_WITH:
    case VM_OP_THROW_VALUE:
    case VM_OP_IS_TRUE_JMP_UP:
    case VM_OP_IS_TRUE_JMP_DOWN:
    case VM_OP_IS_FALSE_JMP_UP:
    case VM_OP_IS_FALSE_JMP_DOWN:
    case VM_OP_VAR_DECL:
    case VM_OP_RETVAL:
    {
      insert_uids_to_lit_id_map (scope_p, om_p, 0x100);
      break;
    }
    case VM_OP_RET:
    case VM_OP_TRY_BLOCK:
    case VM_OP_JMP_UP:
    case VM_OP_JMP_DOWN:
    case VM_OP_JMP_BREAK_CONTINUE:
    case VM_OP_REG_VAR_DECL:
    {
      insert_uids_to_lit_id_map (scope_p, om_p, 0x000);
      break;
    }
    case VM_OP_META:
    {
      switch (om_p->op.data.meta.type)
      {
        case OPCODE_META_TYPE_VARG_PROP_DATA:
        case OPCODE_META_TYPE_VARG_PROP_GETTER:
        case OPCODE_META_TYPE_VARG_PROP_SETTER:
        {
          insert_uids_to_lit_id_map (scope_p, om_p, 0x011);
          break;
        }
        case OPCODE_META_TYPE_VARG:
        case OPCODE_META_TYPE_CATCH_EXCEPTION_IDENTIFIER:
        {
          insert_uids_to_lit_id_map (scope_p, om_p, 0x010);
          break;
        }
        case OPCODE_META_TYPE_UNDEFINED:
        case OPCODE_META_TYPE_END_WITH:
        case OPCODE_META_TYPE_FUNCTION_END:
        case OPCODE_META_TYPE_CATCH:
        case OPCODE_META_TYPE_FINALLY:
        case OPCODE_META_TYPE_END_TRY_CATCH_FINALLY:
        case OPCODE_META_TYPE_CALL_SITE_INFO:
        {
          insert_uids_to_lit_id_map (scope_p, om_p, 0x000);
          break;
        }
      }
      break;
    }

    default:
    {
      JERRY_UNREACHABLE ();
    }
  }
} /* count_new_literals_in_instr */

void dumper_dump_op_meta (op_meta);

void dumper_set_generate_bytecode (bool generate_bytecode)
{
  is_generate_bytecode = generate_bytecode;
} /* dumper_set_generate_bytecode */

/**
 * Allocate next register for intermediate value
 *
 * @return identifier of the allocated register
 */
static vm_idx_t
jsp_alloc_reg_for_temp (void)
{
  JERRY_ASSERT (jsp_reg_max_for_local_var == VM_IDX_EMPTY);
  JERRY_ASSERT (jsp_reg_max_for_args == VM_IDX_EMPTY);

  vm_idx_t next_reg = jsp_reg_next++;

  if (next_reg > VM_REG_GENERAL_LAST)
  {
    /*
     * FIXME:
     *       Implement mechanism, allowing reusage of register variables
     */
    PARSE_ERROR (JSP_EARLY_ERROR_SYNTAX, "Not enough register variables", LIT_ITERATOR_POS_ZERO);
  }

  if (jsp_reg_max_for_temps < next_reg)
  {
    jsp_reg_max_for_temps = next_reg;
  }

  return next_reg;
} /* jsp_alloc_reg_for_temp */

scopes_tree
dumper_get_scope (void)
{
  return current_scope_p;
} /* dumper_get_scope */

void
dumper_set_scope (scopes_tree scope_p)
{
  current_scope_p = scope_p;

  scopes_tmp_lit_set_scope_p = NULL;
} /* dumper_set_scope */

vm_instr_counter_t
dumper_get_current_instr_counter (void)
{
  if (is_generate_bytecode)
  {
    bytecode_data_header_t *bc_header_p = MEM_CP_GET_NON_NULL_POINTER (bytecode_data_header_t,
                                                                       current_scope_p->bc_header_cp);

    return bc_header_p->instrs_count;
  }
  else
  {
    return scopes_tree_instrs_num (current_scope_p);
  }
}

op_meta
dumper_get_op_meta (vm_instr_counter_t pos)
{
  op_meta opm;
  if (is_generate_bytecode)
  {
    bytecode_data_header_t *bc_header_p = MEM_CP_GET_NON_NULL_POINTER (bytecode_data_header_t,
                                                                       current_scope_p->bc_header_cp);
    JERRY_ASSERT (pos < bc_header_p->instrs_count);

    vm_instr_t *instr_p = bc_header_p->instrs_p + pos;

    opm.op = *instr_p;

    uint16_t mask;

    switch (opm.op.op_idx)
    {
      case VM_OP_PROP_GETTER:
      case VM_OP_PROP_SETTER:
      case VM_OP_DELETE_PROP:
      case VM_OP_B_SHIFT_LEFT:
      case VM_OP_B_SHIFT_RIGHT:
      case VM_OP_B_SHIFT_URIGHT:
      case VM_OP_B_AND:
      case VM_OP_B_OR:
      case VM_OP_B_XOR:
      case VM_OP_EQUAL_VALUE:
      case VM_OP_NOT_EQUAL_VALUE:
      case VM_OP_EQUAL_VALUE_TYPE:
      case VM_OP_NOT_EQUAL_VALUE_TYPE:
      case VM_OP_LESS_THAN:
      case VM_OP_GREATER_THAN:
      case VM_OP_LESS_OR_EQUAL_THAN:
      case VM_OP_GREATER_OR_EQUAL_THAN:
      case VM_OP_INSTANCEOF:
      case VM_OP_IN:
      case VM_OP_ADDITION:
      case VM_OP_SUBSTRACTION:
      case VM_OP_DIVISION:
      case VM_OP_MULTIPLICATION:
      case VM_OP_REMAINDER:
      {
        mask = 0x111;
        break;
      }
      case VM_OP_CALL_N:
      case VM_OP_CONSTRUCT_N:
      case VM_OP_FUNC_EXPR_N:
      case VM_OP_DELETE_VAR:
      case VM_OP_TYPEOF:
      case VM_OP_B_NOT:
      case VM_OP_LOGICAL_NOT:
      case VM_OP_POST_INCR:
      case VM_OP_POST_DECR:
      case VM_OP_PRE_INCR:
      case VM_OP_PRE_DECR:
      case VM_OP_UNARY_PLUS:
      case VM_OP_UNARY_MINUS:
      {
        mask = 0x110;
        break;
      }
      case VM_OP_ASSIGNMENT:
      {
        switch (opm.op.data.assignment.type_value_right)
        {
          case OPCODE_ARG_TYPE_SIMPLE:
          case OPCODE_ARG_TYPE_SMALLINT:
          case OPCODE_ARG_TYPE_SMALLINT_NEGATE:
          {
            mask = 0x100;
            break;
          }
          case OPCODE_ARG_TYPE_NUMBER:
          case OPCODE_ARG_TYPE_NUMBER_NEGATE:
          case OPCODE_ARG_TYPE_REGEXP:
          case OPCODE_ARG_TYPE_STRING:
          case OPCODE_ARG_TYPE_VARIABLE:
          {
            mask = 0x101;
            break;
          }
          default:
          {
            JERRY_UNREACHABLE ();
          }
        }
        break;
      }
      case VM_OP_FUNC_DECL_N:
      case VM_OP_FUNC_EXPR_REF:
      case VM_OP_FOR_IN:
      case VM_OP_ARRAY_DECL:
      case VM_OP_OBJ_DECL:
      case VM_OP_WITH:
      case VM_OP_THROW_VALUE:
      case VM_OP_IS_TRUE_JMP_UP:
      case VM_OP_IS_TRUE_JMP_DOWN:
      case VM_OP_IS_FALSE_JMP_UP:
      case VM_OP_IS_FALSE_JMP_DOWN:
      case VM_OP_VAR_DECL:
      case VM_OP_RETVAL:
      {
        mask = 0x100;
        break;
      }
      case VM_OP_RET:
      case VM_OP_TRY_BLOCK:
      case VM_OP_JMP_UP:
      case VM_OP_JMP_DOWN:
      case VM_OP_JMP_BREAK_CONTINUE:
      case VM_OP_REG_VAR_DECL:
      {
        mask = 0x000;
        break;
      }
      case VM_OP_META:
      {
        switch (opm.op.data.meta.type)
        {
          case OPCODE_META_TYPE_VARG_PROP_DATA:
          case OPCODE_META_TYPE_VARG_PROP_GETTER:
          case OPCODE_META_TYPE_VARG_PROP_SETTER:
          {
            mask = 0x011;
            break;
          }
          case OPCODE_META_TYPE_VARG:
          case OPCODE_META_TYPE_CATCH_EXCEPTION_IDENTIFIER:
          {
            mask = 0x010;
            break;
          }
          case OPCODE_META_TYPE_UNDEFINED:
          case OPCODE_META_TYPE_END_WITH:
          case OPCODE_META_TYPE_FUNCTION_END:
          case OPCODE_META_TYPE_CATCH:
          case OPCODE_META_TYPE_FINALLY:
          case OPCODE_META_TYPE_END_TRY_CATCH_FINALLY:
          case OPCODE_META_TYPE_END_FOR_IN:
          case OPCODE_META_TYPE_CALL_SITE_INFO:
          {
            mask = 0x000;
            break;
          }
          default:
          {
            JERRY_UNREACHABLE ();
          }
        }
        break;
      }

      default:
      {
        JERRY_UNREACHABLE ();
      }
    }

    for (uint8_t i = 0; i < 3; i++)
    {
      JERRY_STATIC_ASSERT (VM_IDX_LITERAL_FIRST == 0);

      if (is_possible_literal (mask, i)
          && opm.op.data.raw_args[i] <= VM_IDX_LITERAL_LAST)
      {
        opm.lit_id[i] = bc_get_literal_cp_by_uid (opm.op.data.raw_args[i], bc_header_p, pos);
      }
      else
      {
        opm.lit_id[i] = NOT_A_LITERAL;
      }
    }
  }

  return opm;
}

void
dumper_dump_op_meta (op_meta opm)
{
  if (is_generate_bytecode)
  {
    bytecode_data_header_t *bc_header_p = MEM_CP_GET_NON_NULL_POINTER (bytecode_data_header_t,
                                                                       current_scope_p->bc_header_cp);

  JERRY_ASSERT (bc_header_p->instrs_count < MAX_OPCODES);

#ifdef JERRY_ENABLE_PRETTY_PRINTER
    if (is_print_instrs)
    {
      pp_op_meta (bc_header_p, bc_header_p->instrs_count, opm, false);
    }
#endif

    vm_instr_t *new_instr_place_p = bc_header_p->instrs_p + bc_header_p->instrs_count;

    bc_header_p->instrs_count++;

    JERRY_ASSERT (bc_header_p->instrs_count <= current_scope_p->instrs_count);

    *new_instr_place_p = opm.op;
  }
  else
  {
    count_new_literals_in_instr (current_scope_p, current_scope_p->instrs_count, &opm);

    current_scope_p->instrs_count++;
  }
} /* dumper_dump_op_meta */

void
dumper_rewrite_op_meta (const vm_instr_counter_t loc,
                        op_meta opm)
{
  if (is_generate_bytecode)
  {
    bytecode_data_header_t *bc_header_p = MEM_CP_GET_NON_NULL_POINTER (bytecode_data_header_t,
                                                                       current_scope_p->bc_header_cp);
    JERRY_ASSERT (loc < bc_header_p->instrs_count);

    vm_instr_t *instr_p = bc_header_p->instrs_p + loc;

    *instr_p = opm.op;

#ifdef JERRY_ENABLE_PRETTY_PRINTER
    if (is_print_instrs)
    {
      pp_op_meta (bc_header_p, loc, opm, true);
    }
#endif
  }
} /* dumper_rewrite_op_meta */

#ifdef CONFIG_PARSER_ENABLE_PARSE_TIME_BYTE_CODE_OPTIMIZER
/**
 * Start move of variable values to registers optimization pass
 */
void
dumper_start_move_of_vars_to_regs ()
{
  JERRY_ASSERT (jsp_reg_max_for_local_var == VM_IDX_EMPTY);
  JERRY_ASSERT (jsp_reg_max_for_args == VM_IDX_EMPTY);

  jsp_reg_max_for_local_var = jsp_reg_max_for_temps;
} /* dumper_start_move_of_vars_to_regs */

/**
 * Start move of argument values to registers optimization pass
 *
 * @return true - if optimization can be performed successfully (i.e. there are enough free registers),
 *         false - otherwise.
 */
bool
dumper_start_move_of_args_to_regs (uint32_t args_num) /**< number of arguments */
{
  JERRY_ASSERT (jsp_reg_max_for_args == VM_IDX_EMPTY);

  if (jsp_reg_max_for_local_var == VM_IDX_EMPTY)
  {
    if (args_num + jsp_reg_max_for_temps >= VM_REG_GENERAL_LAST)
    {
      return false;
    }

    jsp_reg_max_for_args = jsp_reg_max_for_temps;
  }
  else
  {
    if (args_num + jsp_reg_max_for_local_var >= VM_REG_GENERAL_LAST)
    {
      return false;
    }

    jsp_reg_max_for_args = jsp_reg_max_for_local_var;
  }

  return true;
} /* dumper_start_move_of_args_to_regs */

/**
 * Try to move local variable to a register
 *
 * Note:
 *      First instruction of the scope should be either func_decl_n or func_expr_n, as the scope is function scope,
 *      and the optimization is not applied to 'new Function ()'-like constructed functions.
 *
 * See also:
 *          parse_source_element_list
 *          parser_parse_program
 *
 * @return true, if optimization performed successfully, i.e.:
 *                - there is a free register to use;
 *                - the variable name is not equal to any of the function's argument names;
 *         false - otherwise.
 */
bool
dumper_try_replace_identifier_name_with_reg (scopes_tree tree, /**< a function scope, created for
                                                                *   function declaration or function expresssion */
                                             op_meta *om_p) /**< operation meta of corresponding
                                                             *   variable declaration */
{
  JERRY_ASSERT (tree == dumper_get_scope ());
  JERRY_ASSERT (tree->type == SCOPE_TYPE_FUNCTION);

  bytecode_data_header_t *bc_header_p = MEM_CP_GET_NON_NULL_POINTER (bytecode_data_header_t,
                                                                     current_scope_p->bc_header_cp);

  lit_cpointer_t lit_cp;
  bool is_arg;

  if (om_p->op.op_idx == VM_OP_VAR_DECL)
  {
    JERRY_ASSERT (om_p->lit_id[0].packed_value != NOT_A_LITERAL.packed_value);
    JERRY_ASSERT (om_p->lit_id[1].packed_value == NOT_A_LITERAL.packed_value);
    JERRY_ASSERT (om_p->lit_id[2].packed_value == NOT_A_LITERAL.packed_value);

    lit_cp = om_p->lit_id[0];

    is_arg = false;
  }
  else
  {
    JERRY_ASSERT (om_p->op.op_idx == VM_OP_META);

    JERRY_ASSERT (om_p->op.data.meta.type == OPCODE_META_TYPE_VARG);
    JERRY_ASSERT (om_p->lit_id[0].packed_value == NOT_A_LITERAL.packed_value);
    JERRY_ASSERT (om_p->lit_id[1].packed_value != NOT_A_LITERAL.packed_value);
    JERRY_ASSERT (om_p->lit_id[2].packed_value == NOT_A_LITERAL.packed_value);

    lit_cp = om_p->lit_id[1];

    is_arg = true;
  }

  vm_idx_t reg;

  if (is_arg)
  {
    JERRY_ASSERT (jsp_reg_max_for_args != VM_IDX_EMPTY);
    JERRY_ASSERT (jsp_reg_max_for_args < VM_REG_GENERAL_LAST);

    reg = ++jsp_reg_max_for_args;
  }
  else
  {
    JERRY_ASSERT (jsp_reg_max_for_local_var != VM_IDX_EMPTY);

    if (jsp_reg_max_for_local_var == VM_REG_GENERAL_LAST)
    {
      /* not enough registers */
      return false;
    }
    JERRY_ASSERT (jsp_reg_max_for_local_var < VM_REG_GENERAL_LAST);

    reg = ++jsp_reg_max_for_local_var;
  }

  for (vm_instr_counter_t instr_pos = 0;
       instr_pos < bc_header_p->instrs_count;
       instr_pos++)
  {
    op_meta om = dumper_get_op_meta (instr_pos);

    vm_op_t opcode = (vm_op_t) om.op.op_idx;

    int args_num = 0;

#define VM_OP_0(opcode_name, opcode_name_uppercase) \
    if (opcode == VM_OP_ ## opcode_name_uppercase) \
    { \
      args_num = 0; \
    }
#define VM_OP_1(opcode_name, opcode_name_uppercase, arg1, arg1_type) \
    if (opcode == VM_OP_ ## opcode_name_uppercase) \
    { \
      JERRY_STATIC_ASSERT (((arg1_type) & VM_OP_ARG_TYPE_TYPE_OF_NEXT) == 0); \
      args_num = 1; \
    }
#define VM_OP_2(opcode_name, opcode_name_uppercase, arg1, arg1_type, arg2, arg2_type) \
    if (opcode == VM_OP_ ## opcode_name_uppercase) \
    { \
      JERRY_STATIC_ASSERT (((arg1_type) & VM_OP_ARG_TYPE_TYPE_OF_NEXT) == 0); \
      JERRY_STATIC_ASSERT (((arg2_type) & VM_OP_ARG_TYPE_TYPE_OF_NEXT) == 0); \
      args_num = 2; \
    }
#define VM_OP_3(opcode_name, opcode_name_uppercase, arg1, arg1_type, arg2, arg2_type, arg3, arg3_type) \
    if (opcode == VM_OP_ ## opcode_name_uppercase) \
    { \
      /*
       * See also:
       *          The loop below
       */ \
      \
      JERRY_ASSERT ((opcode == VM_OP_ASSIGNMENT && (arg2_type) == VM_OP_ARG_TYPE_TYPE_OF_NEXT) \
                    || (opcode != VM_OP_ASSIGNMENT && ((arg2_type) & VM_OP_ARG_TYPE_TYPE_OF_NEXT) == 0)); \
      JERRY_ASSERT ((opcode == VM_OP_META && ((arg1_type) & VM_OP_ARG_TYPE_TYPE_OF_NEXT) != 0) \
                    || (opcode != VM_OP_META && ((arg1_type) & VM_OP_ARG_TYPE_TYPE_OF_NEXT) == 0)); \
      JERRY_STATIC_ASSERT (((arg3_type) & VM_OP_ARG_TYPE_TYPE_OF_NEXT) == 0); \
      args_num = 3; \
    }

#include "vm-opcodes.inc.h"

    for (int arg_index = 0; arg_index < args_num; arg_index++)
    {
      /*
       * 'assignment' and 'meta' are the only opcodes with statically unspecified argument type
       * (checked by assertions above)
       */
      if (opcode == VM_OP_ASSIGNMENT
          && arg_index == 1
          && om.op.data.assignment.type_value_right != VM_OP_ARG_TYPE_VARIABLE)
      {
        break;
      }

      if (opcode == VM_OP_META
          && (((om.op.data.meta.type == OPCODE_META_TYPE_VARG_PROP_DATA
                || om.op.data.meta.type == OPCODE_META_TYPE_VARG_PROP_GETTER
                || om.op.data.meta.type == OPCODE_META_TYPE_VARG_PROP_SETTER)
               && arg_index == 1)
              || om.op.data.meta.type == OPCODE_META_TYPE_END_WITH
              || om.op.data.meta.type == OPCODE_META_TYPE_CATCH
              || om.op.data.meta.type == OPCODE_META_TYPE_FINALLY
              || om.op.data.meta.type == OPCODE_META_TYPE_END_TRY_CATCH_FINALLY
              || om.op.data.meta.type == OPCODE_META_TYPE_END_FOR_IN))
      {
        continue;
      }

      if (om.lit_id[arg_index].packed_value == lit_cp.packed_value)
      {
        om.lit_id[arg_index] = NOT_A_LITERAL;

        om.op.data.raw_args[arg_index] = reg;
      }
    }

    dumper_rewrite_op_meta (instr_pos, om);
  }

  return true;
} /* dumper_try_replace_identifier_name_with_reg */
#endif /* CONFIG_PARSER_ENABLE_PARSE_TIME_BYTE_CODE_OPTIMIZER */

/**
 * Just allocate register for argument that is never used due to duplicated argument names
 */
void
dumper_alloc_reg_for_unused_arg (void)
{
  JERRY_ASSERT (jsp_reg_max_for_args != VM_IDX_EMPTY);
  JERRY_ASSERT (jsp_reg_max_for_args < VM_REG_GENERAL_LAST);

  ++jsp_reg_max_for_args;
} /* dumper_alloc_reg_for_unused_arg */

/**
 * Generate instruction with specified opcode and operands
 *
 * @return VM instruction
 */
static vm_instr_t
jsp_dmp_gen_instr (vm_op_t opcode, /**< operation code */
                   jsp_operand_t ops[], /**< operands */
                   size_t ops_num) /**< operands number */
{
  vm_instr_t instr;

  instr.op_idx = opcode;

  for (size_t i = 0; i < ops_num; i++)
  {
    if (ops[i].is_empty_operand ())
    {
      instr.data.raw_args[i] = VM_IDX_EMPTY;
    }
    else if (ops[i].is_unknown_operand ())
    {
      instr.data.raw_args[i] = VM_IDX_REWRITE_GENERAL_CASE;
    }
    else if (ops[i].is_idx_const_operand ())
    {
      instr.data.raw_args[i] = ops[i].get_idx_const ();
    }
    else if (ops[i].is_smallint_operand ())
    {
      instr.data.raw_args[i] = ops[i].get_smallint_value ();
    }
    else if (ops[i].is_simple_value_operand ())
    {
      instr.data.raw_args[i] = ops[i].get_simple_value ();
    }
    else if (ops[i].is_register_operand () || ops[i].is_this_operand ())
    {
      instr.data.raw_args[i] = ops[i].get_idx ();
    }
    else
    {
      lit_cpointer_t lit_cp;

      if (ops[i].is_identifier_operand ())
      {
        lit_cp = ops[i].get_identifier_name ();
      }
      else
      {
        JERRY_ASSERT (ops[i].is_number_lit_operand ()
                      || ops[i].is_string_lit_operand ()
                      || ops[i].is_regexp_lit_operand ());

        lit_cp = ops[i].get_literal ();
      }

      vm_idx_t idx = VM_IDX_REWRITE_LITERAL_UID;

      if (is_generate_bytecode)
      {
        bytecode_data_header_t *bc_header_p = MEM_CP_GET_NON_NULL_POINTER (bytecode_data_header_t,
                                                                           current_scope_p->bc_header_cp);
        lit_id_hash_table *lit_id_hash_p = MEM_CP_GET_NON_NULL_POINTER (lit_id_hash_table,
                                                                        bc_header_p->lit_id_hash_cp);

        idx = lit_id_hash_table_insert (lit_id_hash_p, bc_header_p->instrs_count, lit_cp);
      }

      instr.data.raw_args[i] = idx;
    }
  }

  for (size_t i = ops_num; i < 3; i++)
  {
    instr.data.raw_args[i] = VM_IDX_EMPTY;
  }

  return instr;
} /* jsp_dmp_gen_instr */

/**
 * Create intermediate instruction description, containing pointers to literals,
 * associated with the instruction's arguments, if there are any.
 *
 * @return intermediate operation description
 */
static op_meta
jsp_dmp_create_op_meta (vm_op_t opcode, /**< opcode */
                        jsp_operand_t ops[], /**< operands */
                        size_t ops_num) /**< operands number */
{
  op_meta ret;

  ret.op = jsp_dmp_gen_instr (opcode, ops, ops_num);

  for (size_t i = 0; i < ops_num; i++)
  {
    if (ops[i].is_number_lit_operand ()
        || ops[i].is_string_lit_operand ()
        || ops[i].is_regexp_lit_operand ())
    {
      ret.lit_id[i] = ops[i].get_literal ();
    }
    else if (ops[i].is_identifier_operand ())
    {
      ret.lit_id[i] = ops[i].get_identifier_name ();
    }
    else
    {
      ret.lit_id[i] = NOT_A_LITERAL;
    }
  }

  for (size_t i = ops_num; i < 3; i++)
  {
    ret.lit_id[i] = NOT_A_LITERAL;
  }

  return ret;
} /* jsp_dmp_create_op_meta */

/**
 * Create intermediate instruction description (for instructions without arguments)
 *
 * See also:
 *          jsp_dmp_create_op_meta
 *
 * @return intermediate instruction description
 */
static op_meta
jsp_dmp_create_op_meta_0 (vm_op_t opcode) /**< opcode */
{
  return jsp_dmp_create_op_meta (opcode, NULL, 0);
} /* jsp_dmp_create_op_meta_0 */

/**
 * Create intermediate instruction description (for instructions with 1 argument)
 *
 * See also:
 *          jsp_dmp_create_op_meta
 *
 * @return intermediate instruction description
 */
static op_meta
jsp_dmp_create_op_meta_1 (vm_op_t opcode, /**< opcode */
                          jsp_operand_t operand1) /**< first operand */
{
  return jsp_dmp_create_op_meta (opcode, &operand1, 1);
} /* jsp_dmp_create_op_meta_1 */

/**
 * Create intermediate instruction description (for instructions with 2 arguments)
 *
 * See also:
 *          jsp_dmp_create_op_meta
 *
 * @return intermediate instruction description
 */
static op_meta
jsp_dmp_create_op_meta_2 (vm_op_t opcode, /**< opcode */
                          jsp_operand_t operand1, /**< first operand */
                          jsp_operand_t operand2) /**< second operand */
{
  jsp_operand_t ops[] = { operand1, operand2 };
  return jsp_dmp_create_op_meta (opcode, ops, 2);
} /* jsp_dmp_create_op_meta_2 */

/**
 * Create intermediate instruction description (for instructions with 3 arguments)
 *
 * See also:
 *          jsp_dmp_create_op_meta
 *
 * @return intermediate instruction description
 */
static op_meta
jsp_dmp_create_op_meta_3 (vm_op_t opcode, /**< opcode */
                          jsp_operand_t operand1, /**< first operand */
                          jsp_operand_t operand2, /**< second operand */
                          jsp_operand_t operand3) /**< third operand */
{
  jsp_operand_t ops[] = { operand1, operand2, operand3 };
  return jsp_dmp_create_op_meta (opcode, ops, 3);
} /* jsp_dmp_create_op_meta_3 */

jsp_operand_t
tmp_operand (void)
{
  return jsp_operand_t::make_reg_operand (jsp_alloc_reg_for_temp ());
}

static void
split_instr_counter (vm_instr_counter_t oc, vm_idx_t *id1, vm_idx_t *id2)
{
  JERRY_ASSERT (id1 != NULL);
  JERRY_ASSERT (id2 != NULL);
  *id1 = (vm_idx_t) (oc >> JERRY_BITSINBYTE);
  *id2 = (vm_idx_t) (oc & ((1 << JERRY_BITSINBYTE) - 1));
  JERRY_ASSERT (oc == vm_calc_instr_counter_from_idx_idx (*id1, *id2));
}

static void
dump_single_address (vm_op_t opcode,
                     jsp_operand_t op)
{
  dumper_dump_op_meta (jsp_dmp_create_op_meta_1 (opcode, op));
}

static void
dump_double_address (vm_op_t opcode,
                     jsp_operand_t res,
                     jsp_operand_t obj)
{
  dumper_dump_op_meta (jsp_dmp_create_op_meta_2 (opcode, res, obj));
}

static void
dump_triple_address (vm_op_t opcode,
                     jsp_operand_t res,
                     jsp_operand_t lhs,
                     jsp_operand_t rhs)
{
  dumper_dump_op_meta (jsp_dmp_create_op_meta_3 (opcode, res, lhs, rhs));
}

static vm_instr_counter_t
get_diff_from (vm_instr_counter_t oc)
{
  return (vm_instr_counter_t) (dumper_get_current_instr_counter () - oc);
}

jsp_operand_t
empty_operand (void)
{
  return jsp_operand_t::make_empty_operand ();
}

bool
operand_is_empty (jsp_operand_t op)
{
  return op.is_empty_operand ();
}

void
dumper_new_statement (void)
{
  jsp_reg_next = VM_REG_GENERAL_FIRST;
}

void
dumper_save_reg_alloc_ctx (vm_idx_t *out_saved_reg_next_p,
                           vm_idx_t *out_saved_reg_max_for_temps_p)
{
  JERRY_ASSERT (jsp_reg_max_for_local_var == VM_IDX_EMPTY);
  JERRY_ASSERT (jsp_reg_max_for_args == VM_IDX_EMPTY);

  *out_saved_reg_next_p = jsp_reg_next;
  *out_saved_reg_max_for_temps_p = jsp_reg_max_for_temps;

  jsp_reg_next = VM_REG_GENERAL_FIRST;
  jsp_reg_max_for_temps = jsp_reg_next;
}

void
dumper_restore_reg_alloc_ctx (vm_idx_t saved_reg_next,
                              vm_idx_t saved_reg_max_for_temps,
                              bool is_overwrite_max)
{
  JERRY_ASSERT (jsp_reg_max_for_local_var == VM_IDX_EMPTY);
  JERRY_ASSERT (jsp_reg_max_for_args == VM_IDX_EMPTY);

  if (is_overwrite_max)
  {
    jsp_reg_max_for_temps = saved_reg_max_for_temps;
  }
  else
  {
    jsp_reg_max_for_temps = JERRY_MAX (jsp_reg_max_for_temps, saved_reg_max_for_temps);
  }

  jsp_reg_next = saved_reg_next;
}

/**
 * Handle start of argument preparation instruction sequence generation
 *
 * Note:
 *      Values of registers, allocated for the code sequence, are not used outside of the sequence,
 *      so they can be reused, reducing register pressure.
 *
 *      To reuse the registers, counter of register allocator is saved, and restored then,
 *      after finishing generation of the code sequence, using dumper_finish_varg_code_sequence.
 *
 * FIXME:
 *       Implement general register allocation mechanism
 *
 * See also:
 *          dumper_finish_varg_code_sequence
 *
 * @return current register allocator's counter (to be restored with dumper_finish_varg_code_sequence)
 */
vm_idx_t
dumper_start_varg_code_sequence (void)
{
  return jsp_reg_next;
} /* dumper_start_varg_code_sequence */

/**
 * Handle finish of argument preparation instruction sequence generation
 *
 * See also:
 *          dumper_start_varg_code_sequence
 */
void
dumper_finish_varg_code_sequence (vm_idx_t reg_alloc_counter) /**< value, returned by corresponding
                                                               *   dumper_start_varg_code_sequence */
{
  jsp_reg_next = reg_alloc_counter;
} /* dumper_finish_varg_code_sequence */

/**
 * Check that byte-code operand refers to 'eval' string
 *
 * @return true - if specified byte-code operand's type is literal, and value of corresponding
 *                literal is equal to LIT_MAGIC_STRING_EVAL string,
 *         false - otherwise.
 */
bool
dumper_is_eval_literal (jsp_operand_t obj) /**< byte-code operand */
{
  /*
   * FIXME: Switch to corresponding magic string
   */
  bool is_eval_lit = (obj.is_identifier_operand ()
                      && lit_literal_equal_type_cstr (lit_get_literal_by_cp (obj.get_identifier_name ()), "eval"));

  return is_eval_lit;
} /* dumper_is_eval_literal */

void
dump_variable_assignment (jsp_operand_t res, jsp_operand_t var)
{
  jsp_operand_t type_operand;

  if (var.is_string_lit_operand ())
  {
    type_operand = jsp_operand_t::make_idx_const_operand (OPCODE_ARG_TYPE_STRING);
  }
  else if (var.is_number_lit_operand ())
  {
    type_operand = jsp_operand_t::make_idx_const_operand (OPCODE_ARG_TYPE_NUMBER);
  }
  else if (var.is_regexp_lit_operand ())
  {
    type_operand = jsp_operand_t::make_idx_const_operand (OPCODE_ARG_TYPE_REGEXP);
  }
  else if (var.is_smallint_operand ())
  {
    type_operand = jsp_operand_t::make_idx_const_operand (OPCODE_ARG_TYPE_SMALLINT);
  }
  else if (var.is_simple_value_operand ())
  {
    type_operand = jsp_operand_t::make_idx_const_operand (OPCODE_ARG_TYPE_SIMPLE);
  }
  else
  {
    JERRY_ASSERT (var.is_identifier_operand ()
                  || var.is_register_operand ()
                  || var.is_this_operand ());

    type_operand = jsp_operand_t::make_idx_const_operand (OPCODE_ARG_TYPE_VARIABLE);
  }

  dump_triple_address (VM_OP_ASSIGNMENT, res, type_operand, var);
}

vm_instr_counter_t
dump_varg_header_for_rewrite (varg_list_type vlt, jsp_operand_t res, jsp_operand_t obj)
{
  vm_instr_counter_t pos = dumper_get_current_instr_counter ();

  switch (vlt)
  {
    case VARG_FUNC_EXPR:
    {
      dump_triple_address (VM_OP_FUNC_EXPR_N,
                           res,
                           obj,
                           jsp_operand_t::make_unknown_operand ());
      break;
    }
    case VARG_CONSTRUCT_EXPR:
    {
      dump_triple_address (VM_OP_CONSTRUCT_N,
                           res,
                           obj,
                           jsp_operand_t::make_unknown_operand ());
      break;
    }
    case VARG_CALL_EXPR:
    {
      dump_triple_address (VM_OP_CALL_N,
                           res,
                           obj,
                           jsp_operand_t::make_unknown_operand ());
      break;
    }
    case VARG_FUNC_DECL:
    {
      dump_double_address (VM_OP_FUNC_DECL_N,
                           obj,
                           jsp_operand_t::make_unknown_operand ());
      break;
    }
    case VARG_ARRAY_DECL:
    {
      dump_double_address (VM_OP_ARRAY_DECL,
                           res,
                           jsp_operand_t::make_unknown_operand ());
      break;
    }
    case VARG_OBJ_DECL:
    {
      dump_double_address (VM_OP_OBJ_DECL,
                           res,
                           jsp_operand_t::make_unknown_operand ());
      break;
    }
  }

  return pos;
}

typedef enum
{
  REWRITE_VARG_HEADER,
  REWRITE_FUNCTION_END,
  REWRITE_CONDITIONAL_CHECK,
  REWRITE_JUMP_TO_END,
  REWRITE_SIMPLE_OR_NESTED_JUMP,
  REWRITE_CASE_CLAUSE,
  REWRITE_DEFAULT_CLAUSE,
  REWRITE_WITH,
  REWRITE_FOR_IN,
  REWRITE_TRY,
  REWRITE_CATCH,
  REWRITE_FINALLY,
  REWRITE_SCOPE_CODE_FLAGS,
  REWRITE_REG_VAR_DECL,
} rewrite_type_t;

static void
dumper_assert_op_fields (rewrite_type_t rewrite_type,
                         op_meta meta)
{
  if (!is_generate_bytecode)
  {
    return;
  }

  if (rewrite_type == REWRITE_FUNCTION_END)
  {
    JERRY_ASSERT (meta.op.op_idx == VM_OP_META);
    JERRY_ASSERT (meta.op.data.meta.type == OPCODE_META_TYPE_FUNCTION_END);
    JERRY_ASSERT (meta.op.data.meta.data_1 == VM_IDX_REWRITE_GENERAL_CASE);
    JERRY_ASSERT (meta.op.data.meta.data_2 == VM_IDX_REWRITE_GENERAL_CASE);
  }
  else if (rewrite_type == REWRITE_CONDITIONAL_CHECK)
  {
    JERRY_ASSERT (meta.op.op_idx == VM_OP_IS_FALSE_JMP_DOWN);
  }
  else if (rewrite_type == REWRITE_JUMP_TO_END)
  {
    JERRY_ASSERT (meta.op.op_idx == VM_OP_JMP_DOWN);
  }
  else if (rewrite_type == REWRITE_CASE_CLAUSE)
  {
    JERRY_ASSERT (meta.op.op_idx == VM_OP_IS_TRUE_JMP_DOWN);
  }
  else if (rewrite_type == REWRITE_DEFAULT_CLAUSE)
  {
    JERRY_ASSERT (meta.op.op_idx == VM_OP_JMP_DOWN);
  }
  else if (rewrite_type == REWRITE_TRY)
  {
    JERRY_ASSERT (meta.op.op_idx == VM_OP_TRY_BLOCK);
  }
  else if (rewrite_type == REWRITE_CATCH)
  {
    JERRY_ASSERT (meta.op.op_idx == VM_OP_META
                  && meta.op.data.meta.type == OPCODE_META_TYPE_CATCH);
  }
  else if (rewrite_type == REWRITE_FINALLY)
  {
    JERRY_ASSERT (meta.op.op_idx == VM_OP_META
                  && meta.op.data.meta.type == OPCODE_META_TYPE_FINALLY);
  }
  else if (rewrite_type == REWRITE_SCOPE_CODE_FLAGS)
  {
    JERRY_ASSERT (meta.op.op_idx == VM_OP_META);
    JERRY_ASSERT (meta.op.data.meta.data_1 == VM_IDX_REWRITE_GENERAL_CASE);
    JERRY_ASSERT (meta.op.data.meta.data_2 == VM_IDX_EMPTY);
  }
  else if (rewrite_type == REWRITE_REG_VAR_DECL)
  {
    JERRY_ASSERT (meta.op.op_idx == VM_OP_REG_VAR_DECL);
  }
  else
  {
    JERRY_UNREACHABLE ();
  }
} /* dumper_assert_op_fields */

void
rewrite_varg_header_set_args_count (size_t args_count,
                                    vm_instr_counter_t pos)
{
  /*
   * FIXME:
   *       Remove formal parameters / arguments number from instruction,
   *       after ecma-values collection would become extendable (issue #310).
   *       In the case, each 'varg' instruction would just append corresponding
   *       argument / formal parameter name to values collection.
   */

  if (!is_generate_bytecode)
  {
    return;
  }

  op_meta om = dumper_get_op_meta (pos);

  switch (om.op.op_idx)
  {
    case VM_OP_FUNC_EXPR_N:
    case VM_OP_CONSTRUCT_N:
    case VM_OP_CALL_N:
    {
      if (args_count > 255)
      {
        PARSE_ERROR (JSP_EARLY_ERROR_SYNTAX,
                     "No more than 255 formal parameters / arguments are currently supported",
                     LIT_ITERATOR_POS_ZERO);
      }
      om.op.data.func_expr_n.arg_list = (vm_idx_t) args_count;
      dumper_rewrite_op_meta (pos, om);
      break;
    }
    case VM_OP_FUNC_DECL_N:
    {
      if (args_count > 255)
      {
        PARSE_ERROR (JSP_EARLY_ERROR_SYNTAX,
                     "No more than 255 formal parameters are currently supported",
                     LIT_ITERATOR_POS_ZERO);
      }
      om.op.data.func_decl_n.arg_list = (vm_idx_t) args_count;
      dumper_rewrite_op_meta (pos, om);
      break;
    }
    case VM_OP_ARRAY_DECL:
    case VM_OP_OBJ_DECL:
    {
      if (args_count > 65535)
      {
        PARSE_ERROR (JSP_EARLY_ERROR_SYNTAX,
                     "No more than 65535 formal parameters are currently supported",
                     LIT_ITERATOR_POS_ZERO);
      }
      om.op.data.obj_decl.list_1 = (vm_idx_t) (args_count >> 8);
      om.op.data.obj_decl.list_2 = (vm_idx_t) (args_count & 0xffu);
      dumper_rewrite_op_meta (pos, om);
      break;
    }
    default:
    {
      JERRY_UNREACHABLE ();
    }
  }
}

/**
 * Dump 'meta' instruction of 'call additional information' type,
 * containing call flags and, optionally, 'this' argument
 */
void
dump_call_additional_info (opcode_call_flags_t flags, /**< call flags */
                           jsp_operand_t this_arg) /**< 'this' argument - if flags
                                                    *   include OPCODE_CALL_FLAGS_HAVE_THIS_ARG,
                                                    *   or empty operand - otherwise */
{
  if (flags & OPCODE_CALL_FLAGS_HAVE_THIS_ARG)
  {
    JERRY_ASSERT (this_arg.is_register_operand () || this_arg.is_this_operand ());
    JERRY_ASSERT (!operand_is_empty (this_arg));
  }
  else
  {
    JERRY_ASSERT (operand_is_empty (this_arg));
  }

  dump_triple_address (VM_OP_META,
                       jsp_operand_t::make_idx_const_operand (OPCODE_META_TYPE_CALL_SITE_INFO),
                       jsp_operand_t::make_idx_const_operand (flags),
                       this_arg);
} /* dump_call_additional_info */

void
dump_varg (jsp_operand_t op)
{
  dump_triple_address (VM_OP_META,
                       jsp_operand_t::make_idx_const_operand (OPCODE_META_TYPE_VARG),
                       op,
                       jsp_operand_t::make_empty_operand ());
}

void
dump_prop_name_and_value (jsp_operand_t name, jsp_operand_t value)
{
  JERRY_ASSERT (name.is_string_lit_operand ());

  dump_triple_address (VM_OP_META,
                       jsp_operand_t::make_idx_const_operand (OPCODE_META_TYPE_VARG_PROP_DATA),
                       name,
                       value);
}

void
dump_prop_getter_decl (jsp_operand_t name, jsp_operand_t func)
{
  JERRY_ASSERT (name.is_string_lit_operand ());
  JERRY_ASSERT (func.is_register_operand ());

  dump_triple_address (VM_OP_META,
                       jsp_operand_t::make_idx_const_operand (OPCODE_META_TYPE_VARG_PROP_GETTER),
                       name,
                       func);
}

void
dump_prop_setter_decl (jsp_operand_t name, jsp_operand_t func)
{
  JERRY_ASSERT (name.is_string_lit_operand ());
  JERRY_ASSERT (func.is_register_operand ());

  dump_triple_address (VM_OP_META,
                       jsp_operand_t::make_idx_const_operand (OPCODE_META_TYPE_VARG_PROP_SETTER),
                       name,
                       func);
}

void
dump_prop_getter (jsp_operand_t obj, jsp_operand_t base, jsp_operand_t prop_name)
{
  dump_triple_address (VM_OP_PROP_GETTER, obj, base, prop_name);
}

void
dump_prop_setter (jsp_operand_t base, jsp_operand_t prop_name, jsp_operand_t obj)
{
  dump_triple_address (VM_OP_PROP_SETTER, base, prop_name, obj);
}

void
dump_delete_prop (jsp_operand_t res,
                  jsp_operand_t base,
                  jsp_operand_t prop_name)
{
  dump_triple_address (VM_OP_DELETE_PROP, res, base, prop_name);
}

void
dump_unary_op (vm_op_t opcode,
               jsp_operand_t res,
               jsp_operand_t op)
{
  dump_double_address (opcode, res, op);
}

void
dump_binary_op (vm_op_t opcode,
                jsp_operand_t res,
                jsp_operand_t op1,
                jsp_operand_t op2)
{
  dump_triple_address (opcode, res, op1, op2);
}

vm_instr_counter_t
dump_conditional_check_for_rewrite (jsp_operand_t op)
{
  vm_instr_counter_t pos = dumper_get_current_instr_counter ();

  dump_triple_address (VM_OP_IS_FALSE_JMP_DOWN,
                       op,
                       jsp_operand_t::make_unknown_operand (),
                       jsp_operand_t::make_unknown_operand ());

  return pos;
}

void
rewrite_conditional_check (vm_instr_counter_t pos)
{
  vm_idx_t id1, id2;
  split_instr_counter (get_diff_from (pos), &id1, &id2);

  op_meta jmp_op_meta = dumper_get_op_meta (pos);
  dumper_assert_op_fields (REWRITE_CONDITIONAL_CHECK, jmp_op_meta);

  jmp_op_meta.op.data.is_false_jmp_down.oc_idx_1 = id1;
  jmp_op_meta.op.data.is_false_jmp_down.oc_idx_2 = id2;

  dumper_rewrite_op_meta (pos, jmp_op_meta);
}

vm_instr_counter_t
dump_jump_to_end_for_rewrite (void)
{
  vm_instr_counter_t pos = dumper_get_current_instr_counter ();

  dump_double_address (VM_OP_JMP_DOWN,
                       jsp_operand_t::make_unknown_operand (),
                       jsp_operand_t::make_unknown_operand ());

  return pos;
}

void
rewrite_jump_to_end (vm_instr_counter_t pos)
{
  vm_idx_t id1, id2;
  split_instr_counter (get_diff_from (pos), &id1, &id2);

  op_meta jmp_op_meta = dumper_get_op_meta (pos);
  dumper_assert_op_fields (REWRITE_JUMP_TO_END, jmp_op_meta);

  jmp_op_meta.op.data.jmp_down.oc_idx_1 = id1;
  jmp_op_meta.op.data.jmp_down.oc_idx_2 = id2;

  dumper_rewrite_op_meta (pos, jmp_op_meta);
}

vm_instr_counter_t
dumper_set_next_iteration_target (void)
{
  return dumper_get_current_instr_counter ();
}

void
dump_continue_iterations_check (vm_instr_counter_t pos,
                                jsp_operand_t op)
{
  const vm_instr_counter_t diff = (vm_instr_counter_t) (dumper_get_current_instr_counter () - pos);
  vm_idx_t id1, id2;
  split_instr_counter (diff, &id1, &id2);

  if (operand_is_empty (op))
  {
    dump_double_address (VM_OP_JMP_UP,
                         jsp_operand_t::make_idx_const_operand (id1),
                         jsp_operand_t::make_idx_const_operand (id2));
  }
  else
  {
    dump_triple_address (VM_OP_IS_TRUE_JMP_UP,
                         op,
                         jsp_operand_t::make_idx_const_operand (id1),
                         jsp_operand_t::make_idx_const_operand (id2));
  }
}

/**
 * Dump template of a jump instruction.
 *
 * Note:
 *      the instruction's flags field is written later (see also: rewrite_simple_or_nested_jump_get_next).
 *
 * @return position of dumped instruction
 */
vm_instr_counter_t
dump_simple_or_nested_jump_for_rewrite (bool is_nested, /**< flag, indicating whether nested (true)
                                                         *   or simple (false) jump should be dumped */
                                        bool is_conditional, /**< flag, indicating whether conditional (true)
                                                              *   or unconditional jump should be dumped */
                                        bool is_inverted_condition, /**< if is_conditional is set, this flag
                                                                     *   indicates whether to invert the condition */
                                        jsp_operand_t cond, /**< condition (for conditional jumps),
                                                             *   empty operand - for non-conditional */
                                        vm_instr_counter_t next_jump_for_tgt_oc) /**< instr counter of next
                                                                                  *   template targetted to
                                                                                  *   the same target - if any,
                                                                                  *   or MAX_OPCODES - otherwise */
{
  vm_idx_t id1, id2;
  split_instr_counter (next_jump_for_tgt_oc, &id1, &id2);

  vm_instr_counter_t ret = dumper_get_current_instr_counter ();

  vm_op_t jmp_opcode;

  if (is_nested)
  {
    jmp_opcode = VM_OP_JMP_BREAK_CONTINUE;
  }
  else if (is_conditional)
  {
    if (is_inverted_condition)
    {
      jmp_opcode = VM_OP_IS_FALSE_JMP_DOWN;
    }
    else
    {
      jmp_opcode = VM_OP_IS_TRUE_JMP_DOWN;
    }
  }
  else
  {
    jmp_opcode = VM_OP_JMP_DOWN;
  }

  if (jmp_opcode == VM_OP_JMP_DOWN
      || jmp_opcode == VM_OP_JMP_BREAK_CONTINUE)
  {
    JERRY_ASSERT (cond.is_empty_operand ());

    dump_double_address (jmp_opcode,
                         jsp_operand_t::make_idx_const_operand (id1),
                         jsp_operand_t::make_idx_const_operand (id2));
  }
  else
  {
    JERRY_ASSERT (!cond.is_empty_operand ());

    JERRY_ASSERT (jmp_opcode == VM_OP_IS_FALSE_JMP_DOWN
                  || jmp_opcode == VM_OP_IS_TRUE_JMP_DOWN);

    dump_triple_address (jmp_opcode,
                         cond,
                         jsp_operand_t::make_idx_const_operand (id1),
                         jsp_operand_t::make_idx_const_operand (id2));
  }

  return ret;
} /* dump_simple_or_nested_jump_for_rewrite */

/**
 * Write jump target position into previously dumped template of jump (simple or nested) instruction
 *
 * @return instr counter value that was encoded in the jump before rewrite
 */
vm_instr_counter_t
rewrite_simple_or_nested_jump_and_get_next (vm_instr_counter_t jump_oc, /**< position of jump to rewrite */
                                            vm_instr_counter_t target_oc) /**< the jump's target */
{
  if (!is_generate_bytecode)
  {
    return MAX_OPCODES;
  }

  op_meta jump_op_meta = dumper_get_op_meta (jump_oc);

  vm_op_t jmp_opcode = (vm_op_t) jump_op_meta.op.op_idx;

  vm_idx_t id1, id2, id1_prev, id2_prev;
  if (target_oc < jump_oc)
  {
    split_instr_counter ((vm_instr_counter_t) (jump_oc - target_oc), &id1, &id2);
  }
  else
  {
    split_instr_counter ((vm_instr_counter_t) (target_oc - jump_oc), &id1, &id2);
  }

  if (jmp_opcode == VM_OP_JMP_DOWN)
  {
    if (target_oc < jump_oc)
    {
      jump_op_meta.op.op_idx = VM_OP_JMP_UP;

      id1_prev = jump_op_meta.op.data.jmp_up.oc_idx_1;
      id2_prev = jump_op_meta.op.data.jmp_up.oc_idx_2;

      jump_op_meta.op.data.jmp_up.oc_idx_1 = id1;
      jump_op_meta.op.data.jmp_up.oc_idx_2 = id2;
    }
    else
    {
      id1_prev = jump_op_meta.op.data.jmp_down.oc_idx_1;
      id2_prev = jump_op_meta.op.data.jmp_down.oc_idx_2;

      jump_op_meta.op.data.jmp_down.oc_idx_1 = id1;
      jump_op_meta.op.data.jmp_down.oc_idx_2 = id2;
    }
  }
  else if (jmp_opcode == VM_OP_IS_TRUE_JMP_DOWN)
  {
    if (target_oc < jump_oc)
    {
      jump_op_meta.op.op_idx = VM_OP_IS_TRUE_JMP_UP;

      id1_prev = jump_op_meta.op.data.is_true_jmp_up.oc_idx_1;
      id2_prev = jump_op_meta.op.data.is_true_jmp_up.oc_idx_2;

      jump_op_meta.op.data.is_true_jmp_up.oc_idx_1 = id1;
      jump_op_meta.op.data.is_true_jmp_up.oc_idx_2 = id2;
    }
    else
    {
      id1_prev = jump_op_meta.op.data.is_true_jmp_down.oc_idx_1;
      id2_prev = jump_op_meta.op.data.is_true_jmp_down.oc_idx_2;

      jump_op_meta.op.data.is_true_jmp_down.oc_idx_1 = id1;
      jump_op_meta.op.data.is_true_jmp_down.oc_idx_2 = id2;
    }
  }
  else if (jmp_opcode == VM_OP_IS_FALSE_JMP_DOWN)
  {
    if (target_oc < jump_oc)
    {
      jump_op_meta.op.op_idx = VM_OP_IS_FALSE_JMP_UP;

      id1_prev = jump_op_meta.op.data.is_false_jmp_up.oc_idx_1;
      id2_prev = jump_op_meta.op.data.is_false_jmp_up.oc_idx_2;

      jump_op_meta.op.data.is_false_jmp_up.oc_idx_1 = id1;
      jump_op_meta.op.data.is_false_jmp_up.oc_idx_2 = id2;
    }
    else
    {
      id1_prev = jump_op_meta.op.data.is_false_jmp_down.oc_idx_1;
      id2_prev = jump_op_meta.op.data.is_false_jmp_down.oc_idx_2;

      jump_op_meta.op.data.is_false_jmp_down.oc_idx_1 = id1;
      jump_op_meta.op.data.is_false_jmp_down.oc_idx_2 = id2;
    }
  }
  else
  {
    JERRY_ASSERT (!is_generate_bytecode || (jmp_opcode == VM_OP_JMP_BREAK_CONTINUE));

    JERRY_ASSERT (target_oc > jump_oc);

    id1_prev = jump_op_meta.op.data.jmp_break_continue.oc_idx_1;
    id2_prev = jump_op_meta.op.data.jmp_break_continue.oc_idx_2;

    jump_op_meta.op.data.jmp_break_continue.oc_idx_1 = id1;
    jump_op_meta.op.data.jmp_break_continue.oc_idx_2 = id2;
  }

  dumper_rewrite_op_meta (jump_oc, jump_op_meta);

  return vm_calc_instr_counter_from_idx_idx (id1_prev, id2_prev);
} /* rewrite_simple_or_nested_jump_get_next */

/**
 * Dump template of 'with' instruction.
 *
 * Note:
 *      the instruction's flags field is written later (see also: rewrite_with).
 *
 * @return position of dumped instruction
 */
vm_instr_counter_t
dump_with_for_rewrite (jsp_operand_t op) /**< jsp_operand_t - result of evaluating Expression
                                          *   in WithStatement */
{
  vm_instr_counter_t oc = dumper_get_current_instr_counter ();

  dump_triple_address (VM_OP_WITH,
                       op,
                       jsp_operand_t::make_unknown_operand (),
                       jsp_operand_t::make_unknown_operand ());

  return oc;
} /* dump_with_for_rewrite */

/**
 * Write position of 'with' block's end to specified 'with' instruction template,
 * dumped earlier (see also: dump_with_for_rewrite).
 */
void
rewrite_with (vm_instr_counter_t oc) /**< instr counter of the instruction template */
{
  vm_idx_t id1, id2;
  split_instr_counter (get_diff_from (oc), &id1, &id2);

  op_meta with_op_meta = dumper_get_op_meta (oc);

  with_op_meta.op.data.with.oc_idx_1 = id1;
  with_op_meta.op.data.with.oc_idx_2 = id2;

  dumper_rewrite_op_meta (oc, with_op_meta);
} /* rewrite_with */

/**
 * Dump 'meta' instruction of 'end with' type
 */
void
dump_with_end (void)
{
  dump_triple_address (VM_OP_META,
                       jsp_operand_t::make_idx_const_operand (OPCODE_META_TYPE_END_WITH),
                       jsp_operand_t::make_empty_operand (),
                       jsp_operand_t::make_empty_operand ());
} /* dump_with_end */

/**
 * Dump template of 'for_in' instruction.
 *
 * Note:
 *      the instruction's flags field is written later (see also: rewrite_for_in).
 *
 * @return position of dumped instruction
 */
vm_instr_counter_t
dump_for_in_for_rewrite (jsp_operand_t op) /**< jsp_operand_t - result of evaluating Expression
                                            *   in for-in statement */
{
  vm_instr_counter_t oc = dumper_get_current_instr_counter ();

  dump_triple_address (VM_OP_FOR_IN,
                       op,
                       jsp_operand_t::make_unknown_operand (),
                       jsp_operand_t::make_unknown_operand ());

  return oc;
} /* dump_for_in_for_rewrite */

/**
 * Write position of 'for_in' block's end to specified 'for_in' instruction template,
 * dumped earlier (see also: dump_for_in_for_rewrite).
 */
void
rewrite_for_in (vm_instr_counter_t oc) /**< instr counter of the instruction template */
{
  vm_idx_t id1, id2;
  split_instr_counter (get_diff_from (oc), &id1, &id2);

  op_meta for_in_op_meta = dumper_get_op_meta (oc);

  for_in_op_meta.op.data.for_in.oc_idx_1 = id1;
  for_in_op_meta.op.data.for_in.oc_idx_2 = id2;

  dumper_rewrite_op_meta (oc, for_in_op_meta);
} /* rewrite_for_in */

/**
 * Dump 'meta' instruction of 'end for_in' type
 */
void
dump_for_in_end (void)
{
  dump_triple_address (VM_OP_META,
                       jsp_operand_t::make_idx_const_operand (OPCODE_META_TYPE_END_FOR_IN),
                       jsp_operand_t::make_empty_operand (),
                       jsp_operand_t::make_empty_operand ());
} /* dump_for_in_end */

vm_instr_counter_t
dump_try_for_rewrite (void)
{
  vm_instr_counter_t pos = dumper_get_current_instr_counter ();

  dump_double_address (VM_OP_TRY_BLOCK,
                       jsp_operand_t::make_unknown_operand (),
                       jsp_operand_t::make_unknown_operand ());

  return pos;
}

void
rewrite_try (vm_instr_counter_t pos)
{
  vm_idx_t id1, id2;
  split_instr_counter (get_diff_from (pos), &id1, &id2);

  op_meta try_op_meta = dumper_get_op_meta (pos);
  dumper_assert_op_fields (REWRITE_TRY, try_op_meta);

  try_op_meta.op.data.try_block.oc_idx_1 = id1;
  try_op_meta.op.data.try_block.oc_idx_2 = id2;

  dumper_rewrite_op_meta (pos, try_op_meta);
}

vm_instr_counter_t
dump_catch_for_rewrite (jsp_operand_t op)
{
  vm_instr_counter_t pos = dumper_get_current_instr_counter ();

  JERRY_ASSERT (op.is_string_lit_operand ());

  dump_triple_address (VM_OP_META,
                       jsp_operand_t::make_idx_const_operand (OPCODE_META_TYPE_CATCH),
                       jsp_operand_t::make_unknown_operand (),
                       jsp_operand_t::make_unknown_operand ());

  dump_triple_address (VM_OP_META,
                       jsp_operand_t::make_idx_const_operand (OPCODE_META_TYPE_CATCH_EXCEPTION_IDENTIFIER),
                       op,
                       jsp_operand_t::make_empty_operand ());

  return pos;
}

void
rewrite_catch (vm_instr_counter_t pos)
{
  vm_idx_t id1, id2;
  split_instr_counter (get_diff_from (pos), &id1, &id2);

  op_meta catch_op_meta = dumper_get_op_meta (pos);
  dumper_assert_op_fields (REWRITE_CATCH, catch_op_meta);

  catch_op_meta.op.data.meta.data_1 = id1;
  catch_op_meta.op.data.meta.data_2 = id2;

  dumper_rewrite_op_meta (pos, catch_op_meta);
}

vm_instr_counter_t
dump_finally_for_rewrite (void)
{
  vm_instr_counter_t pos = dumper_get_current_instr_counter ();

  dump_triple_address (VM_OP_META,
                       jsp_operand_t::make_idx_const_operand (OPCODE_META_TYPE_FINALLY),
                       jsp_operand_t::make_unknown_operand (),
                       jsp_operand_t::make_unknown_operand ());

  return pos;
}

void
rewrite_finally (vm_instr_counter_t pos)
{
  vm_idx_t id1, id2;
  split_instr_counter (get_diff_from (pos), &id1, &id2);

  op_meta finally_op_meta = dumper_get_op_meta (pos);
  dumper_assert_op_fields (REWRITE_FINALLY, finally_op_meta);

  finally_op_meta.op.data.meta.data_1 = id1;
  finally_op_meta.op.data.meta.data_2 = id2;

  dumper_rewrite_op_meta (pos, finally_op_meta);
}

void
dump_end_try_catch_finally (void)
{
  dump_triple_address (VM_OP_META,
                       jsp_operand_t::make_idx_const_operand (OPCODE_META_TYPE_END_TRY_CATCH_FINALLY),
                       jsp_operand_t::make_empty_operand (),
                       jsp_operand_t::make_empty_operand ());
}

void
dump_throw (jsp_operand_t op)
{
  dump_single_address (VM_OP_THROW_VALUE, op);
}

/**
 * Dump instruction designating variable declaration
 */
void
dump_variable_declaration (lit_cpointer_t lit_id) /**< literal which holds variable's name */
{
  jsp_operand_t op_var_name = jsp_operand_t::make_string_lit_operand (lit_id);
  op_meta op = jsp_dmp_create_op_meta (VM_OP_VAR_DECL, &op_var_name, 1);

  scopes_tree_add_var_decl (current_scope_p, op);
} /* dump_variable_declaration */

void
dump_ret (void)
{
  dumper_dump_op_meta (jsp_dmp_create_op_meta_0 (VM_OP_RET));
}

/**
 * Dump 'reg_var_decl' instruction template
 *
 * @return position of the dumped instruction
 */
vm_instr_counter_t
dump_reg_var_decl_for_rewrite (void)
{
  vm_instr_counter_t oc = dumper_get_current_instr_counter ();

  dump_triple_address (VM_OP_REG_VAR_DECL,
                       jsp_operand_t::make_unknown_operand (),
                       jsp_operand_t::make_unknown_operand (),
                       jsp_operand_t::make_unknown_operand ());

  return oc;
} /* dump_reg_var_decl_for_rewrite */

/**
 * Rewrite 'reg_var_decl' instruction's template with current scope's register counts
 */
void
rewrite_reg_var_decl (vm_instr_counter_t reg_var_decl_oc) /**< position of dumped 'reg_var_decl' template */
{
  op_meta opm = dumper_get_op_meta (reg_var_decl_oc);
  dumper_assert_op_fields (REWRITE_REG_VAR_DECL, opm);

  opm.op.data.reg_var_decl.tmp_regs_num = (vm_idx_t) (jsp_reg_max_for_temps - VM_REG_GENERAL_FIRST + 1);

  if (jsp_reg_max_for_local_var != VM_IDX_EMPTY)
  {
    JERRY_ASSERT (jsp_reg_max_for_local_var >= jsp_reg_max_for_temps);
    opm.op.data.reg_var_decl.local_var_regs_num = (vm_idx_t) (jsp_reg_max_for_local_var - jsp_reg_max_for_temps);

    jsp_reg_max_for_local_var = VM_IDX_EMPTY;
  }
  else
  {
    opm.op.data.reg_var_decl.local_var_regs_num = 0;
  }

  if (jsp_reg_max_for_args != VM_IDX_EMPTY)
  {
    if (jsp_reg_max_for_local_var != VM_IDX_EMPTY)
    {
      JERRY_ASSERT (jsp_reg_max_for_args >= jsp_reg_max_for_local_var);
      opm.op.data.reg_var_decl.arg_regs_num = (vm_idx_t) (jsp_reg_max_for_args - jsp_reg_max_for_local_var);
    }
    else
    {
      JERRY_ASSERT (jsp_reg_max_for_args >= jsp_reg_max_for_temps);
      opm.op.data.reg_var_decl.arg_regs_num = (vm_idx_t) (jsp_reg_max_for_args - jsp_reg_max_for_temps);
    }

    jsp_reg_max_for_args = VM_IDX_EMPTY;
  }
  else
  {
    opm.op.data.reg_var_decl.arg_regs_num = 0;
  }

  dumper_rewrite_op_meta (reg_var_decl_oc, opm);
} /* rewrite_reg_var_decl */

void
dump_retval (jsp_operand_t op)
{
  dump_single_address (VM_OP_RETVAL, op);
}

void
dumper_init (bool show_instrs)
{
  is_print_instrs = show_instrs;

  jsp_reg_next = VM_REG_GENERAL_FIRST;
  jsp_reg_max_for_temps = VM_REG_GENERAL_FIRST;
  jsp_reg_max_for_local_var = VM_IDX_EMPTY;
  jsp_reg_max_for_args = VM_IDX_EMPTY;
}

void
dumper_free (void)
{
}
