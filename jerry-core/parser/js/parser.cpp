/* Copyright 2014-2015 Samsung Electronics Co., Ltd.
 * Copyright 2015 University of Szeged.
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

#include "ecma-helpers.h"
#include "hash-table.h"
#include "jrt-libc-includes.h"
#include "jsp-label.h"
#include "jsp-mm.h"
#include "opcodes.h"
#include "opcodes-dumper.h"
#include "parser.h"
#include "re-parser.h"
#include "scopes-tree.h"
#include "serializer.h"
#include "stack.h"
#include "jsp-early-error.h"
#include "vm.h"

/**
 * Flag, indicating whether result of expression
 * evaluation should be stored to 'eval result'
 * temporary variable.
 *
 * In other words, the flag indicates whether
 * 'eval result' store code should be dumped.
 *
 * See also:
 *          parse_expression
 */
typedef enum
{
  JSP_EVAL_RET_STORE_NOT_DUMP, /**< do not dump */
  JSP_EVAL_RET_STORE_DUMP, /**< dump */
} jsp_eval_ret_store_t;

static token tok;
static bool parser_show_instrs = false;

#define EMIT_ERROR(type, MESSAGE) PARSE_ERROR(type, MESSAGE, tok.loc)
#define EMIT_ERROR_VARG(type, MESSAGE, ...) PARSE_ERROR_VARG(type, MESSAGE, tok.loc, __VA_ARGS__)

typedef enum __attr_packed___
{
  /* ECMA-262 v5 expression types */
  JSP_STATE_EXPR_EMPTY              = 0x01, /**< no expression yet (at start) */
  JSP_STATE_EXPR_FUNCTION           = 0x03, /**< FunctionExpression (11.2.5) */
  JSP_STATE_EXPR_MEMBER             = 0x04, /**< MemberExpression (11.2) */
  JSP_STATE_EXPR_CALL               = 0x06, /**< CallExpression (11.2) */
  JSP_STATE_EXPR_LEFTHANDSIDE       = 0x07, /**< LeftHandSideExpression (11.2) */
  JSP_STATE_EXPR_UNARY              = 0x09, /**< UnaryExpression (11.4) */
  JSP_STATE_EXPR_MULTIPLICATIVE     = 0x0A, /**< MultiplicativeExpression (11.5) */
  JSP_STATE_EXPR_ADDITIVE           = 0x0B, /**< AdditiveExpression (11.6) */
  JSP_STATE_EXPR_SHIFT              = 0x0C, /**< ShiftExpression (11.7) */
  JSP_STATE_EXPR_RELATIONAL         = 0x0D, /**< RelationalExpression (11.8) */
  JSP_STATE_EXPR_EQUALITY           = 0x0E, /**< EqualityExpression (11.9) */
  JSP_STATE_EXPR_BITWISE_AND        = 0x0F, /**< BitwiseAndExpression (11.10) */
  JSP_STATE_EXPR_BITWISE_XOR        = 0x10, /**< BitwiseXorExpression (11.10) */
  JSP_STATE_EXPR_BITWISE_OR         = 0x11, /**< BitwiseOrExpression (11.10) */
  JSP_STATE_EXPR_LOGICAL_AND        = 0x12, /**< LogicalAndExpression (11.11) */
  JSP_STATE_EXPR_LOGICAL_OR         = 0x13, /**< LogicalOrExpression (11.11) */
  JSP_STATE_EXPR_CONDITION          = 0x14, /**< ConditionalExpression (11.12) */
  JSP_STATE_EXPR_ASSIGNMENT         = 0x15, /**< AssignmentExpression (11.13) */
  JSP_STATE_EXPR_EXPRESSION         = 0x16, /**< Expression (11.14) */

  JSP_STATE_EXPR_ARRAY_LITERAL      = 0x17, /**< ArrayLiteral (11.1.4) */
  JSP_STATE_EXPR_OBJECT_LITERAL     = 0x18, /**< ObjectLiteral (11.1.5) */

  JSP_STATE_EXPR_DATA_PROP_DECL     = 0x19, /**< a data property (ObjectLiteral, 11.1.5) */
  JSP_STATE_EXPR_ACCESSOR_PROP_DECL = 0x20, /**< an accessor's property getter / setter (ObjectLiteral, 11.1.5) */

  JSP_STATE_STAT_EMPTY              = 0x30, /**< no statement yet (at start) */
  JSP_STATE_STAT_IF_BRANCH_START    = 0x31, /**< IfStatement branch start */
  JSP_STATE_STAT_IF_BRANCH_END      = 0x32, /**< IfStatement branch start */
  JSP_STATE_STAT_STATEMENT          = 0x33, /**< Statement */
  JSP_STATE_STAT_STATEMENT_LIST     = 0x34, /**< Statement list */
  JSP_STATE_STAT_VAR_DECL           = 0x35, /**< VariableStatement */
  JSP_STATE_STAT_DO_WHILE           = 0x36, /**< IterationStatement */
  JSP_STATE_STAT_WHILE              = 0x37,
  JSP_STATE_STAT_FOR_INIT_END       = 0x38,
  JSP_STATE_STAT_FOR_INCREMENT      = 0x39,
  JSP_STATE_STAT_FOR_COND           = 0x40,
  JSP_STATE_STAT_FOR_FINISH         = 0x41,
  JSP_STATE_STAT_FOR_IN_FINISH      = 0x42,
  JSP_STATE_STAT_ITER_FINISH        = 0x43,
  JSP_STATE_STAT_SWITCH_BRANCH      = 0x44,
  JSP_STATE_STAT_SWITCH_FINISH      = 0x45,
  JSP_STATE_STAT_TRY                = 0x46,
  JSP_STATE_STAT_CATCH_FINISH       = 0x47,
  JSP_STATE_STAT_FINALLY_FINISH     = 0x48,
  JSP_STATE_STAT_TRY_FINISH         = 0x49,
  JSP_STATE_STAT_WITH_FINISH        = 0x50,

  JSP_STATE_FUNC_DECL_FINISH        = 0x60,
  JSP_STATE_SOURCE_ELEMENT_LIST     = 0x61,

  JSP_STATE_SOURCE_ELEMENTS_INIT    = 0x62,
  JSP_STATE_SOURCE_ELEMENTS         = 0x63,
  JSP_STATE_SOURCE_ELEMENTS_WAIT_STATEMENT = 0x64,

  JSP_STATE_STAT_BLOCK              = 0x65,
} jsp_state_expr_t;

static jsp_operand_t parse_expression_ (jsp_state_expr_t, bool);

static jsp_operand_t parse_expression (bool, jsp_eval_ret_store_t);

static void parse_statement_ (void);
static void skip_case_clause_body (void);

static bool
token_is (jsp_token_type_t tt)
{
  return (lexer_get_token_type (tok) == tt);
}

static uint16_t
token_data (void)
{
  return tok.uid;
}

/**
 * Get token data as `lit_cpointer_t`
 *
 * @return compressed pointer to token data
 */
static lit_cpointer_t
token_data_as_lit_cp (void)
{
  lit_cpointer_t cp;
  cp.packed_value = tok.uid;

  return cp;
} /* token_data_as_lit_cp */

static void
skip_token (void)
{
  tok = lexer_next_token (false);
}

/**
 * In case a regexp token is scanned as a division operator, rescan it
 */
static void
rescan_regexp_token (void)
{
  lexer_seek (tok.loc);
  tok = lexer_next_token (true);
} /* rescan_regexp_token */

static bool
is_keyword (jsp_token_type_t tt)
{
  return (tt >= TOKEN_TYPE__KEYWORD_BEGIN && tt <= TOKEN_TYPE__KEYWORD_END);
}

static void
assert_keyword (jsp_token_type_t kw)
{
  if (!token_is (kw))
  {
    EMIT_ERROR_VARG (JSP_EARLY_ERROR_SYNTAX, "Expected keyword '%s'", lexer_token_type_to_string (kw));
    JERRY_UNREACHABLE ();
  }
}

static void
current_token_must_be (jsp_token_type_t tt)
{
  if (!token_is (tt))
  {
    EMIT_ERROR_VARG (JSP_EARLY_ERROR_SYNTAX, "Expected '%s' token", lexer_token_type_to_string (tt));
  }
}

static bool
is_strict_mode (void)
{
  return scopes_tree_strict_mode (serializer_get_scope ());
}

#ifdef CONFIG_PARSER_ENABLE_PARSE_TIME_BYTE_CODE_OPTIMIZER
/**
 * Try to perform move (allocation) of variables' values on registers
 *
 * Note:
 *      The optimization is only applied to functions
 *
 * @return number of instructions removed from function's header
 */
static opcode_scope_code_flags_t
jsp_try_move_vars_to_regs (opcode_scope_code_flags_t scope_flags,
                           vm_instr_counter_t *out_number_of_instrs_removed_p)
{
  vm_instr_counter_t number_of_instrs_removed_from_function_header = 0;

  scopes_tree fe_scope_tree = serializer_get_scope ();

  /*
   * We don't try to perform replacement of local variables with registers for global code, eval code.
   *
   * For global and eval code the replacement can be connected with side effects,
   * that currently can only be figured out in runtime. For example, a variable
   * can be redefined as accessor property of the Global object.
   */
  if (fe_scope_tree->type == SCOPE_TYPE_FUNCTION)
  {
    bool may_replace_vars_with_regs = (!fe_scope_tree->ref_eval /* 'eval' can reference variables in a way,
                                                                    * that can't be figured out through static
                                                                    * analysis */
                                       && !fe_scope_tree->ref_arguments /* 'arguments' variable, if declared,
                                                                         * should not be moved to a register,
                                                                         * as it is currently declared in
                                                                         * function's lexical environment
                                                                         * (generally, the problem is the same,
                                                                         *   as with function's arguments) */
                                       && !fe_scope_tree->contains_with /* 'with' create new lexical environment
                                                                         *  and so can change way identifier
                                                                         *  is evaluated */
                                       && !fe_scope_tree->contains_try /* same for 'catch' */
                                       && !fe_scope_tree->contains_delete /* 'delete' handles variable's names,
                                                                           * not values */
                                       && !fe_scope_tree->contains_functions); /* nested functions can reference
                                                                                * variables of current function */

    if (may_replace_vars_with_regs)
    {
      /* no subscopes, as no function declarations / eval etc. in the scope */
      JERRY_ASSERT (fe_scope_tree->t.children == null_list);

      vm_instr_counter_t instr_pos = 0u;

      const vm_instr_counter_t header_oc = instr_pos++;
      op_meta header_opm = scopes_tree_op_meta (fe_scope_tree, header_oc);
      JERRY_ASSERT (header_opm.op.op_idx == VM_OP_FUNC_EXPR_N || header_opm.op.op_idx == VM_OP_FUNC_DECL_N);

      vm_instr_counter_t function_end_pos = instr_pos;
      while (true)
      {
        op_meta meta_opm = scopes_tree_op_meta (fe_scope_tree, function_end_pos);
        JERRY_ASSERT (meta_opm.op.op_idx == VM_OP_META);

        opcode_meta_type meta_type = (opcode_meta_type) meta_opm.op.data.meta.type;

        if (meta_type == OPCODE_META_TYPE_FUNCTION_END)
        {
          /* marker of function argument list end reached */
          break;
        }
        else
        {
          JERRY_ASSERT (meta_type == OPCODE_META_TYPE_VARG);

          function_end_pos++;
        }
      }

      uint32_t args_num = (uint32_t) (function_end_pos - instr_pos);

      dumper_start_move_of_vars_to_regs ();

      /* remove declarations of variables with names equal to an argument's name */
      vm_instr_counter_t var_decl_pos = 0;
      while (var_decl_pos < linked_list_get_length (fe_scope_tree->var_decls))
      {
        op_meta *om_p = (op_meta *) linked_list_element (fe_scope_tree->var_decls, var_decl_pos);
        bool is_removed = false;

        for (vm_instr_counter_t arg_index = instr_pos;
             arg_index < function_end_pos;
             arg_index++)
        {
          op_meta meta_opm = scopes_tree_op_meta (fe_scope_tree, arg_index);
          JERRY_ASSERT (meta_opm.op.op_idx == VM_OP_META);

          JERRY_ASSERT (meta_opm.op.data.meta.data_1 == VM_IDX_REWRITE_LITERAL_UID);
          JERRY_ASSERT (om_p->op.data.var_decl.variable_name == VM_IDX_REWRITE_LITERAL_UID);

          if (meta_opm.lit_id[1].packed_value == om_p->lit_id[0].packed_value)
          {
            linked_list_remove_element (fe_scope_tree->var_decls, var_decl_pos);

            is_removed = true;
            break;
          }
        }

        if (!is_removed)
        {
          if (!dumper_try_replace_identifier_name_with_reg (fe_scope_tree, om_p))
          {
            var_decl_pos++;
          }
          else
          {
            linked_list_remove_element (fe_scope_tree->var_decls, var_decl_pos);
          }
        }
      }

      if (dumper_start_move_of_args_to_regs (args_num))
      {
        scope_flags = (opcode_scope_code_flags_t) (scope_flags | OPCODE_SCOPE_CODE_FLAGS_ARGUMENTS_ON_REGISTERS);

        JERRY_ASSERT (linked_list_get_length (fe_scope_tree->var_decls) == 0);
        scope_flags = (opcode_scope_code_flags_t) (scope_flags | OPCODE_SCOPE_CODE_FLAGS_NO_LEX_ENV);

        /* at this point all arguments can be moved to registers */
        if (header_opm.op.op_idx == VM_OP_FUNC_EXPR_N)
        {
          header_opm.op.data.func_expr_n.arg_list = 0;
        }
        else
        {
          JERRY_ASSERT (header_opm.op.op_idx == VM_OP_FUNC_DECL_N);

          header_opm.op.data.func_decl_n.arg_list = 0;
        }

        scopes_tree_set_op_meta (fe_scope_tree, header_oc, header_opm);

        /*
         * Mark duplicated arguments names as empty,
         * leaving only last declaration for each duplicated
         * argument name
         */
        for (vm_instr_counter_t arg1_index = instr_pos;
             arg1_index < function_end_pos;
             arg1_index++)
        {
          op_meta meta_opm1 = scopes_tree_op_meta (fe_scope_tree, arg1_index);
          JERRY_ASSERT (meta_opm1.op.op_idx == VM_OP_META);

          for (vm_instr_counter_t arg2_index = (vm_instr_counter_t) (arg1_index + 1u);
               arg2_index < function_end_pos;
               arg2_index++)
          {
            op_meta meta_opm2 = scopes_tree_op_meta (fe_scope_tree, arg2_index);
            JERRY_ASSERT (meta_opm2.op.op_idx == VM_OP_META);

            if (meta_opm1.lit_id[1].packed_value == meta_opm2.lit_id[1].packed_value)
            {
              meta_opm1.op.data.meta.data_1 = VM_IDX_EMPTY;
              meta_opm1.lit_id[1] = NOT_A_LITERAL;

              scopes_tree_set_op_meta (fe_scope_tree, arg1_index, meta_opm1);

              break;
            }
          }
        }

        while (true)
        {
          op_meta meta_opm = scopes_tree_op_meta (fe_scope_tree, instr_pos);
          JERRY_ASSERT (meta_opm.op.op_idx == VM_OP_META);

          opcode_meta_type meta_type = (opcode_meta_type) meta_opm.op.data.meta.type;

          if (meta_type == OPCODE_META_TYPE_FUNCTION_END)
          {
            /* marker of function argument list end reached */
            break;
          }
          else
          {
            JERRY_ASSERT (meta_type == OPCODE_META_TYPE_VARG);

            if (meta_opm.op.data.meta.data_1 == VM_IDX_EMPTY)
            {
              JERRY_ASSERT (meta_opm.lit_id[1].packed_value == NOT_A_LITERAL.packed_value);

              dumper_alloc_reg_for_unused_arg ();
            }
            else
            {
              /* the varg specifies argument name, and so should be a string literal */
              JERRY_ASSERT (meta_opm.op.data.meta.data_1 == VM_IDX_REWRITE_LITERAL_UID);
              JERRY_ASSERT (meta_opm.lit_id[1].packed_value != NOT_A_LITERAL.packed_value);

              bool is_replaced = dumper_try_replace_identifier_name_with_reg (fe_scope_tree, &meta_opm);
              JERRY_ASSERT (is_replaced);
            }

            scopes_tree_remove_op_meta (fe_scope_tree, instr_pos);

            number_of_instrs_removed_from_function_header++;
            dumper_decrement_function_end_pos ();
          }
        }
      }
    }
  }

  *out_number_of_instrs_removed_p = number_of_instrs_removed_from_function_header;

  return scope_flags;
}
#endif /* CONFIG_PARSER_ENABLE_PARSE_TIME_BYTE_CODE_OPTIMIZER */

/**
 * Skip block, defined with braces of specified type
 *
 * Note:
 *      Missing corresponding brace is considered a syntax error
 *
 * Note:
 *      Opening brace of the block to skip should be set as current
 *      token when the routine is called
 */
static void
jsp_skip_braces (jsp_token_type_t brace_type) /**< type of the opening brace */
{
  current_token_must_be (brace_type);

  jsp_token_type_t closing_bracket_type;

  if (brace_type == TOK_OPEN_PAREN)
  {
    closing_bracket_type = TOK_CLOSE_PAREN;
  }
  else if (brace_type == TOK_OPEN_BRACE)
  {
    closing_bracket_type = TOK_CLOSE_BRACE;
  }
  else
  {
    JERRY_ASSERT (brace_type == TOK_OPEN_SQUARE);
    closing_bracket_type = TOK_CLOSE_SQUARE;
  }

  skip_token ();

  while (!token_is (closing_bracket_type)
         && !token_is (TOK_EOF))
  {
    if (token_is (TOK_OPEN_PAREN)
        || token_is (TOK_OPEN_BRACE)
        || token_is (TOK_OPEN_SQUARE))
    {
      jsp_skip_braces (lexer_get_token_type (tok));
    }

    skip_token ();
  }

  current_token_must_be (closing_bracket_type);
} /* jsp_skip_braces */

/**
 * Find next token of specified type before the specified location
 *
 * Note:
 *      If skip_brace_blocks is true, every { should correspond to } brace before search end location,
 *      otherwise a syntax error is raised.
 *
 * @return true - if token was found (in the case, it is the current token,
 *                                    and lexer locus points to it),
 *         false - otherwise (in the case, lexer locus points to end_loc).
 */
static bool
jsp_find_next_token_before_the_locus (jsp_token_type_t token_to_find, /**< token to search for (except TOK_EOF) */
                                      locus end_loc, /**< location to search before */
                                      bool skip_brace_blocks) /**< skip blocks, surrounded with { and } braces */
{
  JERRY_ASSERT (token_to_find != TOK_EOF);

  while (lit_utf8_iterator_pos_cmp (tok.loc, end_loc) < 0)
  {
    if (skip_brace_blocks)
    {
      if (token_is (TOK_OPEN_BRACE))
      {
        jsp_skip_braces (TOK_OPEN_BRACE);

        JERRY_ASSERT (token_is (TOK_CLOSE_BRACE));
        skip_token ();

        if (lit_utf8_iterator_pos_cmp (tok.loc, end_loc) >= 0)
        {
          lexer_seek (end_loc);
          tok = lexer_next_token (false);

          return false;
        }
      }
      else if (token_is (TOK_CLOSE_BRACE))
      {
        EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Unmatched } brace");
      }
    }

    if (token_is (token_to_find))
    {
      return true;
    }
    else
    {
      JERRY_ASSERT (!token_is (TOK_EOF));
    }

    skip_token ();
  }

  JERRY_ASSERT (lit_utf8_iterator_pos_cmp (tok.loc, end_loc) == 0);
  return false;
} /* jsp_find_next_token_before_the_locus */

static jsp_operand_t
dump_evaluate_if_reference (jsp_operand_t lhs)
{
  if (lhs.is_identifier_operand ())
  {
    return dump_variable_assignment_res (lhs);
  }
  else if (lhs.is_value_based_reference_operand () && !lhs.is_evaluated_value_based_reference_operand ())
  {
    jsp_operand_t base = lhs.get_value_based_ref_base_identifier ();
    jsp_operand_t prop_name = lhs.get_value_based_ref_prop_name ();

    base = dump_variable_assignment_res (base);

    if (prop_name.is_literal_operand ())
    {
      return jsp_operand_t::make_value_based_ref_operand_vl (base, prop_name.get_literal ());
    }
    else
    {
      return jsp_operand_t::make_value_based_ref_operand_vv (base, prop_name);
    }
  }
  else if (lhs.is_register_operand ()
           && !(lhs.get_idx () >= VM_REG_GENERAL_FIRST && lhs.get_idx () <= VM_REG_GENERAL_LAST))
  {
    return dump_variable_assignment_res (lhs);
  }
  else
  {
    return lhs;
  }
}

/*
 * FIXME:
 *       Move the functionality to dumper
 */
static jsp_operand_t
dump_assignment_of_lhs_if_value_based_reference (jsp_operand_t lhs)
{
  if (lhs.is_value_based_reference_operand ())
  {
    return dump_prop_getter_res (lhs);
  }
  else
  {
    return lhs;
  }
}

static jsp_operand_t
dump_assignment_of_lhs_if_reference (jsp_operand_t lhs)
{
  if (lhs.is_reference_operand ())
  {
    if (lhs.is_value_based_reference_operand ())
    {
      return dump_prop_getter_res (lhs);
    }
    else
    {
      return dump_variable_assignment_res (lhs);
    }
  }
  else if (lhs.is_register_operand ()
           && !(lhs.get_idx () >= VM_REG_GENERAL_FIRST && lhs.get_idx () <= VM_REG_GENERAL_LAST))
  {
    return dump_variable_assignment_res (lhs);
  }
  else
  {
    return lhs;
  }
}

/* property_name
  : Identifier
  | Keyword
  | StringLiteral
  | NumericLiteral
  ;
*/
static jsp_operand_t
parse_property_name (void)
{
  jsp_token_type_t tt = lexer_get_token_type (tok);

  if (is_keyword (tt))
  {
    const char *s = lexer_token_type_to_string (lexer_get_token_type (tok));
    literal_t lit = lit_find_or_create_literal_from_utf8_string ((const lit_utf8_byte_t *) s,
                                                                 (lit_utf8_size_t)strlen (s));
    return literal_operand (lit_cpointer_t::compress (lit));
  }
  else
  {
    switch (tt)
    {
      case TOK_NAME:
      case TOK_STRING:
      {
        return literal_operand (token_data_as_lit_cp ());
      }
      case TOK_NUMBER:
      case TOK_SMALL_INT:
      {
        ecma_number_t num;

        if (lexer_get_token_type (tok) == TOK_NUMBER)
        {
          literal_t num_lit = lit_get_literal_by_cp (token_data_as_lit_cp ());
          JERRY_ASSERT (num_lit->get_type () == LIT_NUMBER_T);
          num = lit_charset_literal_get_number (num_lit);
        }
        else
        {
          num = ((ecma_number_t) token_data ());
        }

        lit_utf8_byte_t buff[ECMA_MAX_CHARS_IN_STRINGIFIED_NUMBER];
        lit_utf8_size_t sz = ecma_number_to_utf8_string (num, buff, sizeof (buff));
        JERRY_ASSERT (sz <= ECMA_MAX_CHARS_IN_STRINGIFIED_NUMBER);

        literal_t str_lit = lit_find_or_create_literal_from_utf8_string (buff, sz);
        return literal_operand (lit_cpointer_t::compress (str_lit));
      }
      case TOK_NULL:
      case TOK_BOOL:
      {
        lit_magic_string_id_t id = (token_is (TOK_NULL)
                                    ? LIT_MAGIC_STRING_NULL
                                    : (tok.uid ? LIT_MAGIC_STRING_TRUE : LIT_MAGIC_STRING_FALSE));
        literal_t lit = lit_find_or_create_literal_from_utf8_string (lit_get_magic_string_utf8 (id),
                                                                     lit_get_magic_string_size (id));
        return literal_operand (lit_cpointer_t::compress (lit));
      }
      default:
      {
        EMIT_ERROR_VARG (JSP_EARLY_ERROR_SYNTAX,
                         "Wrong property name type: %s",
                         lexer_token_type_to_string (lexer_get_token_type (tok)));
      }
    }
  }
}

/**
 * Check for "use strict" in directive prologue
 */
static void
jsp_parse_directive_prologue ()
{
  const locus start_loc = tok.loc;

  /*
   * Check Directive Prologue for Use Strict directive (see ECMA-262 5.1 section 14.1)
   */
  while (token_is (TOK_STRING))
  {
    if (lit_literal_equal_type_cstr (lit_get_literal_by_cp (token_data_as_lit_cp ()), "use strict")
        && lexer_is_no_escape_sequences_in_token_string (tok))
    {
      scopes_tree_set_strict_mode (serializer_get_scope (), true);
      lexer_set_strict_mode (scopes_tree_strict_mode (serializer_get_scope ()));
      break;
    }

    skip_token ();

    if (token_is (TOK_SEMICOLON))
    {
      skip_token ();
    }
  }

  lexer_seek (start_loc);
  skip_token ();
} /* jsp_parse_directive_prologue */

static jsp_operand_t
jsp_start_parse_function_scope (jsp_operand_t func_name,
                                bool is_function_expression,
                                size_t *out_formal_parameters_num_p)
{
  scopes_tree parent_scope = serializer_get_scope ();
  scopes_tree_set_contains_functions (parent_scope);

  scopes_tree func_scope = scopes_tree_init (parent_scope, SCOPE_TYPE_FUNCTION);

  serializer_set_scope (func_scope);
  scopes_tree_set_strict_mode (func_scope, scopes_tree_strict_mode (parent_scope));
  lexer_set_strict_mode (scopes_tree_strict_mode (func_scope));

  /* parse formal parameters list */
  size_t formal_parameters_num = 0;
  jsp_early_error_start_checking_of_vargs ();

  current_token_must_be (TOK_OPEN_PAREN);
  skip_token ();

  JERRY_ASSERT (func_name.is_empty_operand () || func_name.is_literal_operand ());

  varg_list_type vlt = is_function_expression ? VARG_FUNC_EXPR : VARG_FUNC_DECL;

  vm_instr_counter_t varg_header_pos = dump_varg_header_for_rewrite (vlt, func_name);

  while (!token_is (TOK_CLOSE_PAREN))
  {
    current_token_must_be (TOK_NAME);
    jsp_operand_t formal_parameter_name = literal_operand (token_data_as_lit_cp ());
    skip_token ();

    jsp_early_error_add_varg (formal_parameter_name);
    dump_varg (formal_parameter_name);

    formal_parameters_num++;

    if (token_is (TOK_COMMA))
    {
      skip_token ();
    }
    else
    {
      current_token_must_be (TOK_CLOSE_PAREN);
    }
  }

  const jsp_operand_t func = rewrite_varg_header_set_args_count (formal_parameters_num, varg_header_pos);

  dump_function_end_for_rewrite ();

  skip_token ();
  current_token_must_be (TOK_OPEN_BRACE);
  skip_token ();

  jsp_parse_directive_prologue ();

  jsp_early_error_check_for_eval_and_arguments_in_strict_mode (func_name, is_strict_mode (), tok.loc);
  jsp_early_error_check_for_syntax_errors_in_formal_param_list (is_strict_mode (), tok.loc);

  if (out_formal_parameters_num_p != NULL)
  {
    *out_formal_parameters_num_p = formal_parameters_num;
  }

  return func;
}

static void
jsp_finish_parse_function_scope (bool is_function_expression)
{
  scopes_tree func_scope = serializer_get_scope ();
  JERRY_ASSERT (func_scope != NULL && func_scope->type == SCOPE_TYPE_FUNCTION);

  scopes_tree parent_scope = (scopes_tree) func_scope->t.parent;

  current_token_must_be (TOK_CLOSE_BRACE);
  skip_token ();

  dump_ret ();
  rewrite_function_end ();

  serializer_set_scope (parent_scope);

  if (is_function_expression)
  {
    serializer_dump_subscope (func_scope);
    scopes_tree_free (func_scope);
  }

  lexer_set_strict_mode (scopes_tree_strict_mode (parent_scope));
}

typedef struct
{
  jsp_operand_t operand; /**< operand, associated with expression */

  jsp_state_expr_t state; /**< current state */
  jsp_state_expr_t req_expr_type; /**< requested type of expression */

  jsp_token_type_t token_type; /**< token, related to current and, if binary, to previous expression */

  uint8_t is_completed           : 1; /**< the expression parse completed,
                                       *   no more tokens can be added to the expression */
  uint8_t is_list_in_process     : 1; /**< parsing a list, associated with the expression
                                       *   (details depend on current expression type) */
  uint8_t is_no_in_mode          : 1; /**< expression is being parsed in NoIn mode (see also: ECMA-262 v5, 11.8) */
  uint8_t is_fixed_ret_operand   : 1; /**< the expression's evaluation should produce value that should be
                                       *   put to register, specified by operand, specified in state */
  uint8_t is_complex_production  : 1; /**< the expression is being parsed in complex production mode */
  uint8_t is_rewrite_chain_active : 1; /**< flag, indicating whether rewrite chain is associated with current state */
  uint8_t is_raised               : 1; /**< nested label flag*/
  uint8_t var_decl                : 1; /**< this flag tells that we are parsing VariableStatement, not
                                            VariableDeclarationList or VariableDeclaration inside
                                            IterationStatement */
  uint8_t is_default_branch       : 1; /**< marks default branch of switch statement */

  union u
  {
    u (void) { }

    vm_instr_counter_t rewrite_chain; /**< chain of jmp instructions to rewrite */

    struct
    {
      vm_instr_counter_t header_pos; /**< position of a varg header instruction */
      uint32_t list_length;
      vm_idx_t reg_alloc_saved_state;
    } varg_sequence;

    struct
    {
      jsp_operand_t prop_name;
      bool is_setter;
    } accessor_prop_decl;

    struct
    {
      locus loc[2]; /**< remembered location for parsing continuation */
      jsp_label_t label; /**< label for iteration statements processing */
      jsp_label_t *outermost_stmt_label_p; /**< pointer to outermost label, used by labelled and iteration statements */
    } statement;

    struct
    {
      jsp_label_t *prev_label_set_p;
      vm_instr_counter_t scope_code_flags_oc;
      vm_instr_counter_t reg_var_decl_oc;
    } source_elements;

    struct
    {
      vm_instr_counter_t header_pos;
    } for_in;
  } u;
} jsp_state_t;

static_assert (sizeof (jsp_state_t) == 64, "Please, update if size is changed");

/* FIXME: change to dynamic */
#define JSP_STATE_STACK_MAX 256
jsp_state_t jsp_state_stack[JSP_STATE_STACK_MAX];
uint32_t jsp_state_stack_pos = 0;

static void
jsp_state_push (jsp_state_t state)
{
  if (jsp_state_stack_pos == JSP_STATE_STACK_MAX)
  {
    JERRY_UNREACHABLE ();
  }
  else
  {
    jsp_state_stack[jsp_state_stack_pos++] = state;
  }
} /* jsp_state_push */

static jsp_state_t *
jsp_state_top (void)
{
  JERRY_ASSERT (jsp_state_stack_pos > 0);

  return &jsp_state_stack[jsp_state_stack_pos - 1u];
} /* jsp_state_top */

static bool
jsp_is_stack_empty (void)
{
  return (jsp_state_stack_pos == 0);
} /* jsp_is_stack_empty */

static void
jsp_state_pop (void)
{
  JERRY_ASSERT (jsp_state_stack_pos > 0);

  --jsp_state_stack_pos;
} /* jsp_state_pop */

static void
jsp_push_new_expr_state (jsp_state_expr_t expr_type,
                         jsp_state_expr_t req_expr_type,
                         bool in_allowed)
{
  jsp_state_t new_state;

  new_state.state = expr_type;
  new_state.req_expr_type = req_expr_type;
  new_state.operand = empty_operand ();
  new_state.token_type = TOK_EMPTY;

  new_state.is_completed = false;
  new_state.is_list_in_process = false;
  new_state.is_fixed_ret_operand = false;
  new_state.is_complex_production = false;
  new_state.is_rewrite_chain_active = false;
  new_state.is_raised = false;
  new_state.var_decl = false;

  new_state.is_no_in_mode = !in_allowed;

  jsp_state_push (new_state);
} /* jsp_push_new_expr_state */

/*
 * FIXME:
 *       Move to dumper
 */
static vm_instr_counter_t
jsp_start_call_dump (jsp_operand_t obj)
{
  opcode_call_flags_t call_flags = OPCODE_CALL_FLAGS__EMPTY;

  if (obj.is_value_based_reference_operand ())
  {
    if (!obj.is_evaluated_value_based_reference_operand ())
    {
      obj = dump_evaluate_if_reference (obj);
    }

    call_flags = (opcode_call_flags_t) (call_flags | OPCODE_CALL_FLAGS_HAVE_THIS_ARG);

    /*
     * Presence of explicit 'this' argument implies that this is not Direct call to Eval
     *
     * See also:
     *          ECMA-262 v5, 15.2.2.1
     */
  }
  else if (dumper_is_eval_literal (obj))
  {
    call_flags = (opcode_call_flags_t) (call_flags | OPCODE_CALL_FLAGS_DIRECT_CALL_TO_EVAL_FORM);
  }
  else
  {
    /*
     * Note:
     *      If function is called through Identifier, then the obj should be an Identifier reference,
     *      not register variable.
     *      Otherwise, if function is called immediately, without reference (for example, through anonymous
     *      function expression), the obj should be a register variable.
     *
     * See also:
     *          vm_helper_call_get_call_flags_and_this_arg
     */
  }

  jsp_operand_t val = dump_assignment_of_lhs_if_value_based_reference (obj);
  vm_instr_counter_t varg_header_pos = dump_varg_header_for_rewrite (VARG_CALL_EXPR, val);

  if (call_flags != OPCODE_CALL_FLAGS__EMPTY)
  {
    if (call_flags & OPCODE_CALL_FLAGS_HAVE_THIS_ARG)
    {
      dump_call_additional_info (call_flags, obj.get_value_based_ref_base_value ());
    }
    else
    {
      dump_call_additional_info (call_flags, empty_operand ());
    }
  }

  return varg_header_pos;
} /* jsp_start_call_dump */

/*
 * FIXME:
 *       Move to dumper
 */
static jsp_operand_t
jsp_finish_call_dump (uint32_t args_num,
                      vm_instr_counter_t header_pos)
{
  return rewrite_varg_header_set_args_count (args_num, header_pos);
} /* jsp_finish_call_dump */

/*
 * FIXME:
 *       Move to dumper
 */
static vm_instr_counter_t __attr_unused___
jsp_start_construct_dump (jsp_operand_t obj)
{
  return dump_varg_header_for_rewrite (VARG_CONSTRUCT_EXPR,
                                       dump_assignment_of_lhs_if_value_based_reference (obj));
} /* jsp_start_construct_dump */

/*
 * FIXME:
 *       Move to dumper
 */
static jsp_operand_t __attr_unused___
jsp_finish_construct_dump (uint32_t args_num,
                      vm_instr_counter_t header_pos)
{
  return rewrite_varg_header_set_args_count (args_num, header_pos);
} /* jsp_finish_construct_dump */

static lit_cpointer_t
jsp_get_prop_name_after_dot (void)
{
  if (token_is (TOK_NAME))
  {
    return token_data_as_lit_cp ();
  }
  else if (is_keyword (lexer_get_token_type (tok)))
  {
    const char *s = lexer_token_type_to_string (lexer_get_token_type (tok));
    literal_t lit = lit_find_or_create_literal_from_utf8_string ((lit_utf8_byte_t *) s,
                                                                 (lit_utf8_size_t) strlen (s));
    if (lit == NULL)
    {
      EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Expected identifier");
    }

    return lit_cpointer_t::compress (lit);
  }
  else if (token_is (TOK_BOOL) || token_is (TOK_NULL))
  {
    lit_magic_string_id_t id = (token_is (TOK_NULL)
                                ? LIT_MAGIC_STRING_NULL
                                : (tok.uid ? LIT_MAGIC_STRING_TRUE : LIT_MAGIC_STRING_FALSE));
    literal_t lit = lit_find_or_create_literal_from_utf8_string (lit_get_magic_string_utf8 (id),
                                                                 lit_get_magic_string_size (id));

    return lit_cpointer_t::compress (lit);
  }
  else
  {
    EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Expected identifier");
  }
} /* jsp_get_prop_name_after_dot */

/**
 * Parse an expression
 *
 * expression
 *  : assignment_expression (LT!* ',' LT!* assignment_expression)*
 *  ;
 *
 * @return jsp_operand_t which holds result of expression
 */
static jsp_operand_t __attr_unused___
parse_expression_ (jsp_state_expr_t req_expr,
                   bool in_allowed) /**< flag indicating if 'in' is allowed inside expression to parse */
{
  jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, req_expr, in_allowed);

  uint32_t start_pos = jsp_state_stack_pos;

  while (true)
  {
    bool is_subexpr_end = false;
    jsp_operand_t subexpr_operand;
    jsp_state_expr_t subexpr_type;

    jsp_state_t* state_p = jsp_state_top ();

    if (state_p->state == state_p->req_expr_type && state_p->is_completed)
    {
      (void) jsp_is_stack_empty ();

      if (start_pos == jsp_state_stack_pos) // FIXME: jsp_is_stack_empty ()
      {
        /* expression parse finished */
        jsp_operand_t ret = state_p->operand;
        jsp_state_pop ();

        return ret;
      }
      else
      {
        is_subexpr_end = true;

        subexpr_operand = state_p->operand;
        subexpr_type = state_p->state;
        JERRY_ASSERT (state_p->is_completed);
        jsp_state_pop ();

        state_p = jsp_state_top ();
      }
    }
    else
    {
      /*
       * Any expression production, if parse of the production is not stopped because required
       * production type was reached, eventually becomes Expression production.
       *
       * Because there are no any expression production higher than Expression,
       * its invalid to reach Expression production type if required production is lower
       * (i.e. is not Expression production type).
       */
      JERRY_ASSERT (!(state_p->state == JSP_STATE_EXPR_EXPRESSION && state_p->req_expr_type != JSP_STATE_EXPR_EXPRESSION));
    }

    const bool in_allowed = !state_p->is_no_in_mode;

    if (state_p->state == JSP_STATE_EXPR_EMPTY)
    {
      rescan_regexp_token ();

      /* no subexpressions can occur, as expression parse is just started */
      JERRY_ASSERT (!is_subexpr_end);
      JERRY_ASSERT (!state_p->is_completed);

      jsp_token_type_t tt = lexer_get_token_type (tok);
      if ((tt >= TOKEN_TYPE__UNARY_BEGIN
           && tt <= TOKEN_TYPE__UNARY_END)
          || tt == TOK_KW_DELETE
          || tt == TOK_KW_VOID
          || tt == TOK_KW_TYPEOF)
      {
        /* UnaryExpression */
        state_p->state = JSP_STATE_EXPR_UNARY;
        state_p->token_type = tt;

        if (tt == TOK_KW_DELETE)
        {
          scopes_tree_set_contains_delete (serializer_get_scope ());
        }

        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_UNARY, in_allowed);
      }
      else if (token_is (TOK_KW_FUNCTION))
      {
        /* FunctionExpression */
        state_p->state = JSP_STATE_EXPR_FUNCTION;
      }
      else if (token_is (TOK_OPEN_SQUARE))
      {
        /* ArrayLiteral */
        vm_instr_counter_t varg_header_pos = dump_varg_header_for_rewrite (VARG_ARRAY_DECL, empty_operand ());

        state_p->state = JSP_STATE_EXPR_ARRAY_LITERAL;
        state_p->is_list_in_process = true;
        state_p->u.varg_sequence.list_length = 0;
        state_p->u.varg_sequence.header_pos = varg_header_pos;
      }
      else if (token_is (TOK_OPEN_BRACE))
      {
        /* ObjectLiteral */
        vm_instr_counter_t varg_header_pos = dump_varg_header_for_rewrite (VARG_OBJ_DECL, empty_operand ());
        jsp_early_error_start_checking_of_prop_names ();

        state_p->state = JSP_STATE_EXPR_OBJECT_LITERAL;
        state_p->is_list_in_process = true;
        state_p->u.varg_sequence.list_length = 0;
        state_p->u.varg_sequence.header_pos = varg_header_pos;
      }
      else
      {
        /* MemberExpression (PrimaryExpression is immediately promoted to MemberExpression) */
        state_p->state = JSP_STATE_EXPR_MEMBER;

        switch (lexer_get_token_type (tok))
        {
          case TOK_OPEN_PAREN:
          {
            state_p->token_type = TOK_OPEN_PAREN;

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
            break;
          }
          case TOK_KW_THIS:
          {
            state_p->operand = dump_this_res ();
            break;
          }
          case TOK_KW_NEW:
          {
            state_p->state = JSP_STATE_EXPR_MEMBER;
            state_p->token_type = TOK_KW_NEW;

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_MEMBER, true);
            break;
          }
          case TOK_NAME:
          {
            if (lit_literal_equal_type_cstr (lit_get_literal_by_cp (token_data_as_lit_cp ()), "arguments"))
            {
              scopes_tree_set_arguments_used (serializer_get_scope ());
            }
            if (lit_literal_equal_type_cstr (lit_get_literal_by_cp (token_data_as_lit_cp ()), "eval"))
            {
              scopes_tree_set_eval_used (serializer_get_scope ());
            }

            state_p->operand = jsp_operand_t::make_identifier_operand (token_data_as_lit_cp ());

            break;
          }
          case TOK_REGEXP:
          {
            state_p->operand = tmp_operand ();
            dump_regexp_assignment (state_p->operand, token_data_as_lit_cp ());
            break;
          }
          case TOK_NULL:
          {
            state_p->operand = tmp_operand ();
            dump_null_assignment (state_p->operand);
            break;
          }
          case TOK_BOOL:
          {
            state_p->operand = tmp_operand ();
            dump_boolean_assignment (state_p->operand, (bool) token_data ());
            break;
          }
          case TOK_SMALL_INT:
          {
            state_p->operand = tmp_operand ();
            dump_smallint_assignment (state_p->operand, (vm_idx_t) token_data ());
            break;
          }
          case TOK_NUMBER:
          {
            state_p->operand = tmp_operand ();
            dump_number_assignment (state_p->operand, token_data_as_lit_cp ());
            break;
          }
          case TOK_STRING:
          {
            state_p->operand = tmp_operand ();
            dump_string_assignment (state_p->operand, token_data_as_lit_cp ());
            break;
          }
          default:
          {
            EMIT_ERROR_VARG (JSP_EARLY_ERROR_SYNTAX,
                             "Unknown token %s",
                             lexer_token_type_to_string (lexer_get_token_type (tok)));
          }
        }
      }

      skip_token ();
    }
    else if (state_p->state == JSP_STATE_SOURCE_ELEMENT_LIST)
    {
      JERRY_ASSERT (!state_p->is_completed);

      /* FIXME: merge with parse_statement_ */
      parse_statement_ ();

      state_p->is_completed = true;
    }
    else if (state_p->state == JSP_STATE_EXPR_FUNCTION)
    {
      JERRY_ASSERT (!state_p->is_completed);

      if (is_subexpr_end)
      {
        jsp_finish_parse_function_scope (true);

        state_p->state = JSP_STATE_EXPR_MEMBER;
      }
      else
      {
        jsp_operand_t name;
        if (token_is (TOK_NAME))
        {
          name = literal_operand (token_data_as_lit_cp ());
          skip_token ();
        }
        else
        {
          name = empty_operand ();
        }

        state_p->operand = jsp_start_parse_function_scope (name, true, NULL);

        jsp_push_new_expr_state (JSP_STATE_SOURCE_ELEMENT_LIST, JSP_STATE_SOURCE_ELEMENT_LIST, true);
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_DATA_PROP_DECL)
    {
      JERRY_ASSERT (!state_p->is_completed);

      if (is_subexpr_end)
      {
        JERRY_ASSERT (subexpr_type == JSP_STATE_EXPR_ASSIGNMENT);

        jsp_operand_t prop_name = state_p->operand;
        jsp_operand_t value = subexpr_operand;

        JERRY_ASSERT (prop_name.is_literal_operand ());

        dump_prop_name_and_value (prop_name, dump_assignment_of_lhs_if_value_based_reference (value));
        jsp_early_error_add_prop_name (prop_name, PROP_DATA);

        state_p->is_completed = true;
      }
      else
      {
        JERRY_ASSERT (state_p->operand.is_empty_operand ());
        state_p->operand = parse_property_name ();
        skip_token ();

        JERRY_ASSERT (token_is (TOK_COLON));
        skip_token ();

        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_ACCESSOR_PROP_DECL)
    {
      JERRY_ASSERT (!state_p->is_completed);

      if (is_subexpr_end)
      {
        jsp_finish_parse_function_scope (true);

        jsp_operand_t prop_name = state_p->u.accessor_prop_decl.prop_name;
        jsp_operand_t func = state_p->operand;
        bool is_setter = state_p->u.accessor_prop_decl.is_setter;

        if (is_setter)
        {
          dump_prop_setter_decl (prop_name, func);
        }
        else
        {
          dump_prop_getter_decl (prop_name, func);
        }

        state_p->is_completed = true;
      }
      else
      {
        bool is_setter;

        current_token_must_be (TOK_NAME);

        lit_cpointer_t lit_cp = token_data_as_lit_cp ();

        if (lit_literal_equal_type_cstr (lit_get_literal_by_cp (lit_cp), "get"))
        {
          is_setter = false;
        }
        else if (lit_literal_equal_type_cstr (lit_get_literal_by_cp (lit_cp), "set"))
        {
          is_setter = true;
        }
        else
        {
          EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Invalid property declaration");
        }

        skip_token ();

        jsp_operand_t prop_name = parse_property_name ();
        skip_token ();

        jsp_early_error_add_prop_name (prop_name, is_setter ? PROP_SET : PROP_GET);

        size_t formal_parameters_num;
        const jsp_operand_t func = jsp_start_parse_function_scope (empty_operand (), true, &formal_parameters_num);

        size_t req_num_of_formal_parameters = is_setter ? 1 : 0;

        if (req_num_of_formal_parameters != formal_parameters_num)
        {
          EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Invalid number of formal parameters");
        }

        JERRY_ASSERT (state_p->operand.is_empty_operand ());
        state_p->operand = func;

        state_p->u.accessor_prop_decl.prop_name = prop_name;
        state_p->u.accessor_prop_decl.is_setter = is_setter;

        jsp_push_new_expr_state (JSP_STATE_SOURCE_ELEMENT_LIST, JSP_STATE_SOURCE_ELEMENT_LIST, true);
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_OBJECT_LITERAL)
    {
      JERRY_ASSERT (!state_p->is_completed);
      JERRY_ASSERT (state_p->is_list_in_process);

      if (is_subexpr_end)
      {
        JERRY_ASSERT (subexpr_type == JSP_STATE_EXPR_DATA_PROP_DECL
                      || subexpr_type == JSP_STATE_EXPR_ACCESSOR_PROP_DECL);

        state_p->u.varg_sequence.list_length++;

        dumper_finish_varg_code_sequence (state_p->u.varg_sequence.reg_alloc_saved_state);

        if (token_is (TOK_COMMA))
        {
          skip_token ();
        }
        else
        {
          current_token_must_be (TOK_CLOSE_BRACE);
        }
      }

      if (token_is (TOK_CLOSE_BRACE))
      {
        jsp_early_error_check_for_duplication_of_prop_names (is_strict_mode (), tok.loc);

        skip_token ();

        state_p->operand = rewrite_varg_header_set_args_count (state_p->u.varg_sequence.list_length,
                                                               state_p->u.varg_sequence.header_pos);

        state_p->state = JSP_STATE_EXPR_MEMBER;
        state_p->is_list_in_process = false;
      }
      else
      {
        state_p->u.varg_sequence.reg_alloc_saved_state = dumper_start_varg_code_sequence ();

        locus start_pos = tok.loc;
        skip_token ();

        jsp_state_expr_t expr_type;
        if (token_is (TOK_COLON))
        {
          expr_type = JSP_STATE_EXPR_DATA_PROP_DECL;
        }
        else
        {
          expr_type = JSP_STATE_EXPR_ACCESSOR_PROP_DECL;
        }

        lexer_seek (start_pos);
        skip_token ();

        jsp_push_new_expr_state (expr_type, expr_type, true);
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_ARRAY_LITERAL)
    {
      JERRY_ASSERT (!state_p->is_completed);
      JERRY_ASSERT (state_p->is_list_in_process);

      if (is_subexpr_end)
      {
        subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);

        dump_varg (subexpr_operand);

        state_p->u.varg_sequence.list_length++;

        dumper_finish_varg_code_sequence (state_p->u.varg_sequence.reg_alloc_saved_state);

        if (token_is (TOK_COMMA))
        {
          skip_token ();
        }
        else
        {
          current_token_must_be (TOK_CLOSE_SQUARE);
        }
      }
      else
      {
        if (token_is (TOK_CLOSE_SQUARE))
        {
          skip_token ();

          state_p->operand = rewrite_varg_header_set_args_count (state_p->u.varg_sequence.list_length,
                                                                 state_p->u.varg_sequence.header_pos);

          state_p->state = JSP_STATE_EXPR_MEMBER;
          state_p->is_list_in_process = false;
        }
        else if (token_is (TOK_COMMA))
        {
          while (token_is (TOK_COMMA))
          {
            skip_token ();

            vm_idx_t reg_alloc_saved_state = dumper_start_varg_code_sequence ();

            dump_varg (dump_array_hole_assignment_res ());

            state_p->u.varg_sequence.list_length++;

            dumper_finish_varg_code_sequence (reg_alloc_saved_state);
          }
        }
        else
        {
          state_p->u.varg_sequence.reg_alloc_saved_state = dumper_start_varg_code_sequence ();

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);
        }
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_MEMBER)
    {
      if (state_p->is_completed)
      {
        if (token_is (TOK_OPEN_PAREN))
        {
          state_p->state = JSP_STATE_EXPR_CALL;
          state_p->is_completed = false;

          /* propagate to CallExpression */
          state_p->state = JSP_STATE_EXPR_CALL;
        }
        else
        {
          /* propagate to LeftHandSideExpression */
          state_p->state = JSP_STATE_EXPR_LEFTHANDSIDE;
          JERRY_ASSERT (state_p->is_completed);
        }
      }
      else
      {
        if (is_subexpr_end)
        {
          if (state_p->is_list_in_process)
          {
            JERRY_ASSERT (state_p->token_type == TOK_KW_NEW);
            JERRY_ASSERT (subexpr_type == JSP_STATE_EXPR_ASSIGNMENT);

            subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);
            dump_varg (subexpr_operand);

            dumper_finish_varg_code_sequence (state_p->u.varg_sequence.reg_alloc_saved_state);

            state_p->u.varg_sequence.list_length++;

            if (token_is (TOK_CLOSE_PAREN))
            {
              state_p->token_type = TOK_EMPTY;
              state_p->is_list_in_process = false;
              state_p->operand = jsp_finish_construct_dump (state_p->u.varg_sequence.list_length,
                                                            state_p->u.varg_sequence.header_pos);
            }
            else
            {
              current_token_must_be (TOK_COMMA);

              jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);

              state_p->u.varg_sequence.reg_alloc_saved_state = dumper_start_varg_code_sequence ();
            }

            skip_token ();
          }
          else if (state_p->token_type == TOK_OPEN_PAREN)
          {
            JERRY_ASSERT (state_p->operand.is_empty_operand ());

            state_p->operand = subexpr_operand;
            state_p->token_type = TOK_EMPTY;

            current_token_must_be (TOK_CLOSE_PAREN);
            skip_token ();
          }
          else if (state_p->token_type == TOK_KW_NEW)
          {
            JERRY_ASSERT (subexpr_type == JSP_STATE_EXPR_MEMBER);
            JERRY_ASSERT (state_p->operand.is_empty_operand ());
            JERRY_ASSERT (!subexpr_operand.is_empty_operand ());

            state_p->operand = subexpr_operand;

            vm_instr_counter_t header_pos = jsp_start_construct_dump (state_p->operand);

            bool is_arg_list_implicit = true;
            bool is_arg_list_empty = true;

            if (token_is (TOK_OPEN_PAREN))
            {
              skip_token ();

              is_arg_list_implicit = false;

              if (token_is (TOK_CLOSE_PAREN))
              {
                skip_token ();
              }
              else
              {
                is_arg_list_empty = false;
              }
            }

            if (!is_arg_list_implicit && !is_arg_list_empty)
            {
              state_p->is_list_in_process = true;
              state_p->u.varg_sequence.list_length = 0;
              state_p->u.varg_sequence.header_pos = header_pos;
              state_p->u.varg_sequence.reg_alloc_saved_state = dumper_start_varg_code_sequence ();

              jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);
            }
            else
            {
              state_p->token_type = TOK_EMPTY;

              if (is_arg_list_implicit)
              {
                state_p->state = JSP_STATE_EXPR_MEMBER;
                state_p->is_completed = true;
              }

              state_p->operand = jsp_finish_construct_dump (0, header_pos);
            }
          }
          else
          {
            JERRY_ASSERT (state_p->token_type == TOK_OPEN_SQUARE);
            state_p->token_type = TOK_EMPTY;

            current_token_must_be (TOK_CLOSE_SQUARE);
            skip_token ();

            subexpr_operand = dump_assignment_of_lhs_if_reference (subexpr_operand);

            if (state_p->operand.is_identifier_operand ())
            {
              state_p->operand = jsp_operand_t::make_value_based_ref_operand_lv (state_p->operand.get_identifier_name (),
                                                                              subexpr_operand);
            }
            else
            {
              state_p->operand = jsp_operand_t::make_value_based_ref_operand_vv (state_p->operand, subexpr_operand);
            }
          }
        }
        else if (token_is (TOK_OPEN_SQUARE))
        {
          skip_token ();

          state_p->token_type = TOK_OPEN_SQUARE;
          state_p->operand = dump_assignment_of_lhs_if_value_based_reference (state_p->operand);

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
        }
        else if (token_is (TOK_DOT))
        {
          skip_token ();

          state_p->operand = dump_assignment_of_lhs_if_value_based_reference (state_p->operand);

          if (state_p->operand.is_identifier_operand ())
          {
            state_p->operand = jsp_operand_t::make_value_based_ref_operand_ll (state_p->operand.get_identifier_name (),
                                                                            jsp_get_prop_name_after_dot ());
          }
          else
          {
            state_p->operand = jsp_operand_t::make_value_based_ref_operand_vl (state_p->operand,
                                                                            jsp_get_prop_name_after_dot ());
          }

          skip_token ();
        }
        else
        {
          state_p->is_completed = true;
        }
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_CALL)
    {
      JERRY_ASSERT (!state_p->is_completed);

      if (is_subexpr_end)
      {
        if (state_p->is_list_in_process)
        {
          JERRY_ASSERT (subexpr_type == JSP_STATE_EXPR_ASSIGNMENT);

          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);
          dump_varg (subexpr_operand);

          dumper_finish_varg_code_sequence (state_p->u.varg_sequence.reg_alloc_saved_state);

          state_p->u.varg_sequence.list_length++;

          if (token_is (TOK_CLOSE_PAREN))
          {
            state_p->is_list_in_process = false;

            state_p->operand = jsp_finish_call_dump (state_p->u.varg_sequence.list_length,
                                                     state_p->u.varg_sequence.header_pos);
          }
          else
          {
            current_token_must_be (TOK_COMMA);

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);

            state_p->u.varg_sequence.reg_alloc_saved_state = dumper_start_varg_code_sequence ();
          }
        }
        else
        {
          JERRY_ASSERT (state_p->token_type == TOK_OPEN_SQUARE);
          state_p->token_type = TOK_EMPTY;

          current_token_must_be (TOK_CLOSE_SQUARE);

          subexpr_operand = dump_assignment_of_lhs_if_reference (subexpr_operand);
          state_p->operand = jsp_operand_t::make_value_based_ref_operand_vv (state_p->operand,
                                                                             subexpr_operand);
        }

        skip_token ();
      }
      else
      {
        if (token_is (TOK_OPEN_PAREN))
        {
          skip_token ();

          vm_instr_counter_t header_pos = jsp_start_call_dump (state_p->operand);

          if (token_is (TOK_CLOSE_PAREN))
          {
            skip_token ();

            state_p->operand = jsp_finish_call_dump (0, header_pos);
          }
          else
          {
            state_p->is_list_in_process = true;
            state_p->u.varg_sequence.list_length = 0;
            state_p->u.varg_sequence.header_pos = header_pos;
            state_p->u.varg_sequence.reg_alloc_saved_state = dumper_start_varg_code_sequence ();

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);
          }
        }
        else if (token_is (TOK_OPEN_SQUARE))
        {
          skip_token ();

          state_p->token_type = TOK_OPEN_SQUARE;
          state_p->operand = dump_assignment_of_lhs_if_reference (state_p->operand);

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
        }
        else if (token_is (TOK_DOT))
        {
          skip_token ();

          state_p->operand = dump_assignment_of_lhs_if_reference (state_p->operand);

          state_p->operand = jsp_operand_t::make_value_based_ref_operand_vl (state_p->operand,
                                                                             jsp_get_prop_name_after_dot ());
          skip_token ();
        }
        else
        {
          state_p->state = JSP_STATE_EXPR_LEFTHANDSIDE;
          state_p->is_completed = true;
        }
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_LEFTHANDSIDE)
    {
      JERRY_ASSERT (state_p->is_completed);

      if (is_subexpr_end)
      {
        jsp_token_type_t tt = state_p->token_type;

        state_p->state = JSP_STATE_EXPR_ASSIGNMENT;
        state_p->token_type = TOK_EMPTY;
        state_p->is_completed = true;

        JERRY_ASSERT (tt >= TOKEN_TYPE__ASSIGNMENTS_BEGIN && tt <= TOKEN_TYPE__ASSIGNMENTS_END);

        subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);

        if (tt == TOK_EQ)
        {
          state_p->operand = dump_prop_setter_or_variable_assignment_res (state_p->operand, subexpr_operand);
        }
        else if (tt == TOK_MULT_EQ)
        {
          state_p->operand = dump_prop_setter_or_multiplication_res (state_p->operand, subexpr_operand);
        }
        else if (tt == TOK_DIV_EQ)
        {
          state_p->operand = dump_prop_setter_or_division_res (state_p->operand, subexpr_operand);
        }
        else if (tt == TOK_MOD_EQ)
        {
          state_p->operand = dump_prop_setter_or_remainder_res (state_p->operand, subexpr_operand);
        }
        else if (tt == TOK_PLUS_EQ)
        {
          state_p->operand = dump_prop_setter_or_addition_res (state_p->operand, subexpr_operand);
        }
        else if (tt == TOK_MINUS_EQ)
        {
          state_p->operand = dump_prop_setter_or_substraction_res (state_p->operand, subexpr_operand);
        }
        else if (tt == TOK_LSHIFT_EQ)
        {
          state_p->operand = dump_prop_setter_or_left_shift_res (state_p->operand, subexpr_operand);
        }
        else if (tt == TOK_RSHIFT_EQ)
        {
          state_p->operand = dump_prop_setter_or_right_shift_res (state_p->operand, subexpr_operand);
        }
        else if (tt == TOK_RSHIFT_EX_EQ)
        {
          state_p->operand = dump_prop_setter_or_right_shift_ex_res (state_p->operand, subexpr_operand);
        }
        else if (tt == TOK_AND_EQ)
        {
          state_p->operand = dump_prop_setter_or_bitwise_and_res (state_p->operand, subexpr_operand);
        }
        else if (tt == TOK_XOR_EQ)
        {
          state_p->operand = dump_prop_setter_or_bitwise_xor_res (state_p->operand, subexpr_operand);
        }
        else
        {
          JERRY_ASSERT (tt == TOK_OR_EQ);

          state_p->operand = dump_prop_setter_or_bitwise_or_res (state_p->operand, subexpr_operand);
        }
      }
      else
      {
        JERRY_ASSERT (state_p->token_type == TOK_EMPTY);

        if (token_is (TOK_DOUBLE_PLUS)
            && !lexer_is_preceded_by_newlines (tok))
        {
          jsp_early_error_check_for_eval_and_arguments_in_strict_mode (state_p->operand, is_strict_mode (), tok.loc);
          if (!state_p->operand.is_reference_operand ())
          {
            PARSE_ERROR (JSP_EARLY_ERROR_REFERENCE, "Invalid left-hand-side expression", tok.loc);
          }

          state_p->operand = dump_post_increment_res (state_p->operand);
          state_p->state = JSP_STATE_EXPR_UNARY;
          JERRY_ASSERT (state_p->is_completed);

          skip_token ();
        }
        else if (token_is (TOK_DOUBLE_MINUS)
                 && !lexer_is_preceded_by_newlines (tok))
        {
          jsp_early_error_check_for_eval_and_arguments_in_strict_mode (state_p->operand, is_strict_mode (), tok.loc);
          if (!state_p->operand.is_reference_operand ())
          {
            PARSE_ERROR (JSP_EARLY_ERROR_REFERENCE, "Invalid left-hand-side expression", tok.loc);
          }

          state_p->operand = dump_post_decrement_res (state_p->operand);
          state_p->state = JSP_STATE_EXPR_UNARY;
          JERRY_ASSERT (state_p->is_completed);

          skip_token ();
        }
        else
        {
          jsp_token_type_t tt = lexer_get_token_type (tok);

          if (tt >= TOKEN_TYPE__ASSIGNMENTS_BEGIN && tt <= TOKEN_TYPE__ASSIGNMENTS_END)
          {
            jsp_early_error_check_for_eval_and_arguments_in_strict_mode (state_p->operand, is_strict_mode (), tok.loc);

            if (!state_p->operand.is_reference_operand ())
            {
              PARSE_ERROR (JSP_EARLY_ERROR_REFERENCE, "Invalid left-hand-side expression", tok.loc);
            }

            /* skip the assignment operator */
            skip_token ();
            state_p->token_type = tt;

            if (state_p->operand.is_value_based_reference_operand ()
                && !state_p->operand.is_evaluated_value_based_reference_operand ())
            {
              state_p->operand = dump_evaluate_if_reference (state_p->operand);
            }

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, in_allowed);
          }
          else
          {
            state_p->state = JSP_STATE_EXPR_UNARY;
          }
        }
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_UNARY)
    {
      if (state_p->is_completed)
      {
        /* propagate to MultiplicativeExpression */
        state_p->state = JSP_STATE_EXPR_MULTIPLICATIVE;
        state_p->is_completed = false;
      }
      else
      {
        JERRY_ASSERT (is_subexpr_end);

        if (state_p->token_type == TOK_DOUBLE_PLUS)
        {
          jsp_early_error_check_for_eval_and_arguments_in_strict_mode (subexpr_operand, is_strict_mode (), tok.loc);

          if (!subexpr_operand.is_reference_operand ())
          {
            PARSE_ERROR (JSP_EARLY_ERROR_REFERENCE, "Invalid left-hand-side expression", tok.loc);
          }

          state_p->operand = dump_pre_increment_res (subexpr_operand);
        }
        else if (state_p->token_type == TOK_DOUBLE_MINUS)
        {
          jsp_early_error_check_for_eval_and_arguments_in_strict_mode (subexpr_operand, is_strict_mode (), tok.loc);

          if (!subexpr_operand.is_reference_operand ())
          {
            PARSE_ERROR (JSP_EARLY_ERROR_REFERENCE, "Invalid left-hand-side expression", tok.loc);
          }

          state_p->operand = dump_pre_decrement_res (subexpr_operand);
        }
        else if (state_p->token_type == TOK_PLUS)
        {
          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);
          state_p->operand = dump_unary_plus_res (subexpr_operand);
        }
        else if (state_p->token_type == TOK_MINUS)
        {
          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);
          state_p->operand = dump_unary_minus_res (subexpr_operand);
        }
        else if (state_p->token_type == TOK_COMPL)
        {
          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);
          state_p->operand = dump_bitwise_not_res (subexpr_operand);
        }
        else if (state_p->token_type == TOK_NOT)
        {
          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);
          state_p->operand = dump_logical_not_res (subexpr_operand);
        }
        else if (state_p->token_type == TOK_KW_DELETE)
        {
          if (subexpr_operand.is_identifier_operand ())
          {
            jsp_early_error_check_delete (is_strict_mode (), tok.loc);
          }

          state_p->operand = dump_delete_res (subexpr_operand);
        }
        else if (state_p->token_type == TOK_KW_VOID)
        {
          dump_evaluate_if_reference (subexpr_operand);
          state_p->operand = dump_undefined_assignment_res ();
        }
        else
        {
          JERRY_ASSERT (state_p->token_type == TOK_KW_TYPEOF);

          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);
          state_p->operand = dump_typeof_res (subexpr_operand);
        }

        state_p->token_type = TOK_EMPTY;
        state_p->is_completed = true;
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_MULTIPLICATIVE)
    {
      if (state_p->is_completed)
      {
        /* propagate to AdditiveExpression */
        state_p->state = JSP_STATE_EXPR_ADDITIVE;
        state_p->is_completed = false;
      }
      else
      {
        if (is_subexpr_end)
        {
          state_p->operand = dump_assignment_of_lhs_if_value_based_reference (state_p->operand);
          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);

          if (state_p->token_type == TOK_MULT)
          {
            dump_multiplication (state_p->operand, state_p->operand, subexpr_operand);
          }
          else if (state_p->token_type == TOK_DIV)
          {
            dump_division (state_p->operand, state_p->operand, subexpr_operand);
          }
          else
          {
            JERRY_ASSERT (state_p->token_type == TOK_MOD);

            dump_remainder (state_p->operand, state_p->operand, subexpr_operand);
          }

          state_p->token_type = TOK_EMPTY;
        }
        else if (lexer_get_token_type (tok) >= TOKEN_TYPE__MULTIPLICATIVE_BEGIN
                 && lexer_get_token_type (tok) <= TOKEN_TYPE__MULTIPLICATIVE_END)
        {
          state_p->operand = dump_assignment_of_lhs_if_reference (state_p->operand);
          state_p->token_type = lexer_get_token_type (tok);

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_UNARY, in_allowed);

          skip_token ();
        }
        else
        {
          state_p->is_completed = true;
        }
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_ADDITIVE)
    {
      if (state_p->is_completed)
      {
        /* propagate to ShiftExpression */
        state_p->state = JSP_STATE_EXPR_SHIFT;
        state_p->is_completed = false;
      }
      else
      {
        if (is_subexpr_end)
        {
          state_p->operand = dump_assignment_of_lhs_if_value_based_reference (state_p->operand);
          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);

          if (state_p->token_type == TOK_PLUS)
          {
            dump_addition (state_p->operand, state_p->operand, subexpr_operand);
          }
          else
          {
            JERRY_ASSERT (state_p->token_type == TOK_MINUS);

            dump_substraction (state_p->operand, state_p->operand, subexpr_operand);
          }

          state_p->token_type = TOK_EMPTY;
        }
        else if (lexer_get_token_type (tok) >= TOKEN_TYPE__ADDITIVE_BEGIN
                 && lexer_get_token_type (tok) <= TOKEN_TYPE__ADDITIVE_END)
        {
          state_p->operand = dump_assignment_of_lhs_if_reference (state_p->operand);
          state_p->token_type = lexer_get_token_type (tok);

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_MULTIPLICATIVE, in_allowed);

          skip_token ();
        }
        else
        {
          state_p->is_completed = true;
        }
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_SHIFT)
    {
      if (state_p->is_completed)
      {
        /* propagate to RelationalExpression */
        state_p->state = JSP_STATE_EXPR_RELATIONAL;
        state_p->is_completed = false;
      }
      else
      {
        if (is_subexpr_end)
        {
          state_p->operand = dump_assignment_of_lhs_if_value_based_reference (state_p->operand);
          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);

          if (state_p->token_type == TOK_LSHIFT)
          {
            dump_left_shift (state_p->operand, state_p->operand, subexpr_operand);
          }
          else if (state_p->token_type == TOK_RSHIFT)
          {
            dump_right_shift (state_p->operand, state_p->operand, subexpr_operand);
          }
          else
          {
            JERRY_ASSERT (state_p->token_type == TOK_RSHIFT_EX);

            dump_right_shift_ex (state_p->operand, state_p->operand, subexpr_operand);
          }

          state_p->token_type = TOK_EMPTY;
        }
        else if (lexer_get_token_type (tok) >= TOKEN_TYPE__SHIFT_BEGIN
                 && lexer_get_token_type (tok) <= TOKEN_TYPE__SHIFT_END)
        {
          state_p->operand = dump_assignment_of_lhs_if_reference (state_p->operand);
          state_p->token_type = lexer_get_token_type (tok);

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ADDITIVE, in_allowed);

          skip_token ();
        }
        else
        {
          state_p->is_completed = true;
        }
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_RELATIONAL)
    {
      if (state_p->is_completed)
      {
        /* propagate to EqualityExpression */
        state_p->state = JSP_STATE_EXPR_EQUALITY;
        state_p->is_completed = false;
      }
      else
      {
        if (is_subexpr_end)
        {
          state_p->operand = dump_assignment_of_lhs_if_value_based_reference (state_p->operand);
          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);

          if (state_p->token_type == TOK_LESS)
          {
            dump_less_than (state_p->operand, state_p->operand, subexpr_operand);
          }
          else if (state_p->token_type == TOK_GREATER)
          {
            dump_greater_than (state_p->operand, state_p->operand, subexpr_operand);
          }
          else if (state_p->token_type == TOK_LESS_EQ)
          {
            dump_less_or_equal_than (state_p->operand, state_p->operand, subexpr_operand);
          }
          else if (state_p->token_type == TOK_GREATER_EQ)
          {
            dump_greater_or_equal_than (state_p->operand, state_p->operand, subexpr_operand);
          }
          else if (state_p->token_type == TOK_KW_INSTANCEOF)
          {
            dump_instanceof (state_p->operand, state_p->operand, subexpr_operand);
          }
          else
          {
            JERRY_ASSERT (state_p->token_type == TOK_KW_IN);
            JERRY_ASSERT (in_allowed);

            dump_in (state_p->operand, state_p->operand, subexpr_operand);
          }

          state_p->token_type = TOK_EMPTY;
        }
        else if ((lexer_get_token_type (tok) >= TOKEN_TYPE__RELATIONAL_BEGIN
                  && lexer_get_token_type (tok) <= TOKEN_TYPE__RELATIONAL_END)
                 || lexer_get_token_type (tok) == TOK_KW_INSTANCEOF
                 || (in_allowed && lexer_get_token_type (tok) == TOK_KW_IN))
        {
          state_p->operand = dump_assignment_of_lhs_if_reference (state_p->operand);
          state_p->token_type = lexer_get_token_type (tok);

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_SHIFT, in_allowed);

          skip_token ();
        }
        else
        {
          state_p->is_completed = true;
        }
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_EQUALITY)
    {
      if (state_p->is_completed)
      {
        /* propagate to BitwiseAndExpression */
        state_p->state = JSP_STATE_EXPR_BITWISE_AND;
        state_p->is_completed = false;
      }
      else
      {
        if (is_subexpr_end)
        {
          state_p->operand = dump_assignment_of_lhs_if_value_based_reference (state_p->operand);
          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);

          if (state_p->token_type == TOK_DOUBLE_EQ)
          {
            dump_equal_value (state_p->operand, state_p->operand, subexpr_operand);
          }
          else if (state_p->token_type == TOK_NOT_EQ)
          {
            dump_not_equal_value (state_p->operand, state_p->operand, subexpr_operand);
          }
          else if (state_p->token_type == TOK_TRIPLE_EQ)
          {
            dump_equal_value_type (state_p->operand, state_p->operand, subexpr_operand);
          }
          else
          {
            JERRY_ASSERT (state_p->token_type == TOK_NOT_DOUBLE_EQ);

            dump_not_equal_value_type (state_p->operand, state_p->operand, subexpr_operand);
          }

          state_p->token_type = TOK_EMPTY;
        }
        else if (lexer_get_token_type (tok) >= TOKEN_TYPE__EQUALITY_BEGIN
                 && lexer_get_token_type (tok) <= TOKEN_TYPE__EQUALITY_END)
        {
          state_p->operand = dump_assignment_of_lhs_if_reference (state_p->operand);
          state_p->token_type = lexer_get_token_type (tok);

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_RELATIONAL, in_allowed);

          skip_token ();
        }
        else
        {
          state_p->is_completed = true;
        }
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_BITWISE_AND)
    {
      /* FIXME: Consider merging BitwiseOR / BitwiseXOR / BitwiseAND productions
       * into one production with different operators, taking their precedence into account */

      if (state_p->is_completed)
      {
        /* propagate to BitwiseXorExpression */
        state_p->state = JSP_STATE_EXPR_BITWISE_XOR;
        state_p->is_completed = false;
      }
      else
      {
        if (is_subexpr_end)
        {
          state_p->operand = dump_assignment_of_lhs_if_value_based_reference (state_p->operand);
          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);

          JERRY_ASSERT (state_p->token_type == TOK_AND);

          state_p->token_type = TOK_EMPTY;
          dump_bitwise_and (state_p->operand, state_p->operand, subexpr_operand);
        }
        else if (token_is (TOK_AND))
        {
          skip_token ();

          state_p->operand = dump_assignment_of_lhs_if_reference (state_p->operand);
          state_p->token_type = TOK_AND;

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EQUALITY, in_allowed);
        }
        else
        {
          state_p->is_completed = true;
        }
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_BITWISE_XOR)
    {
      if (state_p->is_completed)
      {
        /* propagate to BitwiseOrExpression */
        state_p->state = JSP_STATE_EXPR_BITWISE_OR;
        state_p->is_completed = false;
      }
      else
      {
        if (is_subexpr_end)
        {
          state_p->operand = dump_assignment_of_lhs_if_value_based_reference (state_p->operand);
          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);

          JERRY_ASSERT (state_p->token_type == TOK_XOR);

          state_p->token_type = TOK_EMPTY;
          dump_bitwise_xor (state_p->operand, state_p->operand, subexpr_operand);
        }
        else if (token_is (TOK_XOR))
        {
          skip_token ();

          state_p->operand = dump_assignment_of_lhs_if_reference (state_p->operand);
          state_p->token_type = TOK_XOR;

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_BITWISE_AND, in_allowed);
        }
        else
        {
          state_p->is_completed = true;
        }
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_BITWISE_OR)
    {
      if (state_p->is_completed)
      {
        /* propagate to LogicalAndExpression */
        state_p->state = JSP_STATE_EXPR_LOGICAL_AND;
        state_p->is_completed = false;
      }
      else
      {
        if (is_subexpr_end)
        {
          state_p->operand = dump_assignment_of_lhs_if_value_based_reference (state_p->operand);
          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);

          JERRY_ASSERT (state_p->token_type == TOK_OR);

          state_p->token_type = TOK_EMPTY;
          dump_bitwise_or (state_p->operand, state_p->operand, subexpr_operand);
        }
        else if (token_is (TOK_OR))
        {
          skip_token ();

          state_p->operand = dump_assignment_of_lhs_if_reference (state_p->operand);
          state_p->token_type = TOK_OR;

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_BITWISE_XOR, in_allowed);
        }
        else
        {
          state_p->is_completed = true;
        }
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_LOGICAL_AND)
    {
      if (state_p->is_completed)
      {
        /* propagate to LogicalOrExpression */
        state_p->state = JSP_STATE_EXPR_LOGICAL_OR;
        state_p->is_completed = false;
      }
      else
      {
        if (is_subexpr_end)
        {
          state_p->operand = dump_assignment_of_lhs_if_value_based_reference (state_p->operand);
          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);

          JERRY_ASSERT (state_p->token_type == TOK_DOUBLE_AND);

          JERRY_ASSERT (state_p->operand.is_register_operand ());

          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);

          dump_variable_assignment (state_p->operand, subexpr_operand);

          state_p->token_type = TOK_EMPTY;
        }
        else
        {
          JERRY_ASSERT (state_p->token_type == TOK_EMPTY);

          if (token_is (TOK_DOUBLE_AND))
          {
            /* ECMA-262 v5, 11.11 (complex LogicalAndExpression) */
            skip_token ();

            /*
             * FIXME:
             *       Consider eliminating COMPLEX_PRODUCTION flag through implementing establishing a general operand
             *       management for expressions
             */
            if (!state_p->is_complex_production)
            {
              state_p->is_complex_production = true;

              state_p->is_rewrite_chain_active = true;
              state_p->u.rewrite_chain = MAX_OPCODES;

              JERRY_ASSERT (!state_p->is_fixed_ret_operand);

              jsp_operand_t ret = tmp_operand ();

              state_p->operand = dump_assignment_of_lhs_if_value_based_reference (state_p->operand);
              dump_variable_assignment (ret, state_p->operand);

              state_p->is_fixed_ret_operand = true;
              state_p->operand = ret;
            }

            JERRY_ASSERT (state_p->is_complex_production);
            JERRY_ASSERT (state_p->is_rewrite_chain_active);

            state_p->u.rewrite_chain = dump_simple_or_nested_jump_for_rewrite (VM_OP_IS_FALSE_JMP_DOWN,
                                                                               state_p->operand,
                                                                               state_p->u.rewrite_chain);

            state_p->token_type = TOK_DOUBLE_AND;

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_BITWISE_OR, in_allowed);
          }
          else
          {
            /* end of LogicalAndExpression */
            JERRY_ASSERT (state_p->token_type == TOK_EMPTY);

            vm_instr_counter_t target_oc = serializer_get_current_instr_counter ();

            if (state_p->is_rewrite_chain_active)
            {
              while (state_p->u.rewrite_chain != MAX_OPCODES)
              {
                state_p->u.rewrite_chain = rewrite_simple_or_nested_jump_and_get_next (state_p->u.rewrite_chain,
                                                                                       target_oc);
              }

              state_p->is_rewrite_chain_active = false;
            }

            state_p->is_complex_production = false;

            state_p->is_completed = true;
          }
        }
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_LOGICAL_OR)
    {
      if (state_p->is_completed)
      {
        /* switching to ConditionalExpression */
        if (token_is (TOK_QUERY))
        {
          state_p->state = JSP_STATE_EXPR_CONDITION;
          state_p->is_completed = false;

          /* ECMA-262 v5, 11.12 */
          skip_token ();

          dump_conditional_check_for_rewrite (state_p->operand);

          state_p->token_type = TOK_QUERY;

          JERRY_ASSERT (!state_p->is_fixed_ret_operand);

          state_p->is_fixed_ret_operand = true;
          state_p->operand = tmp_operand ();

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);
        }
        else
        {
          /* just propagate */
          state_p->state = JSP_STATE_EXPR_ASSIGNMENT;
          JERRY_ASSERT (state_p->is_completed);
        }
      }
      else
      {
        if (is_subexpr_end)
        {
          subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);

          JERRY_ASSERT (state_p->token_type == TOK_DOUBLE_OR);

          JERRY_ASSERT (state_p->operand.is_register_operand ());
          dump_variable_assignment (state_p->operand, subexpr_operand);

          state_p->token_type = TOK_EMPTY;
        }
        else
        {
          JERRY_ASSERT (state_p->token_type == TOK_EMPTY);

          if (token_is (TOK_DOUBLE_OR))
          {
            /* ECMA-262 v5, 11.11 (complex LogicalOrExpression) */
            skip_token ();

            /*
             * FIXME:
             *       Consider eliminating COMPLEX_PRODUCTION flag through implementing establishing a general operand
             *       management for expressions
             */
            if (!state_p->is_complex_production)
            {
              state_p->is_complex_production = true;

              state_p->is_rewrite_chain_active = true;
              state_p->u.rewrite_chain = MAX_OPCODES;

              jsp_operand_t ret = tmp_operand ();

              state_p->operand = dump_assignment_of_lhs_if_value_based_reference (state_p->operand);
              dump_variable_assignment (ret, state_p->operand);

              JERRY_ASSERT (!state_p->is_fixed_ret_operand);
              state_p->is_fixed_ret_operand = true;

              state_p->operand = ret;
            }

            JERRY_ASSERT (state_p->is_complex_production);
            JERRY_ASSERT (state_p->is_rewrite_chain_active);

            state_p->u.rewrite_chain = dump_simple_or_nested_jump_for_rewrite (VM_OP_IS_TRUE_JMP_DOWN,
                                                                               state_p->operand,
                                                                               state_p->u.rewrite_chain);

            state_p->token_type = TOK_DOUBLE_OR;

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_LOGICAL_AND, in_allowed);
          }
          else
          {
            /* end of LogicalOrExpression */
            JERRY_ASSERT (state_p->token_type == TOK_EMPTY);

            vm_instr_counter_t target_oc = serializer_get_current_instr_counter ();

            if (state_p->is_rewrite_chain_active)
            {
              while (state_p->u.rewrite_chain != MAX_OPCODES)
              {
                state_p->u.rewrite_chain = rewrite_simple_or_nested_jump_and_get_next (state_p->u.rewrite_chain,
                                                                                       target_oc);
              }

              state_p->is_rewrite_chain_active = false;
            }

            state_p->is_complex_production = false;

            state_p->is_completed = true;
          }
        }
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_ASSIGNMENT)
    {
      /* assignment production can't be continued at the point */
      JERRY_ASSERT (!is_subexpr_end);

      JERRY_ASSERT (state_p->is_completed);
      JERRY_ASSERT (state_p->token_type == TOK_EMPTY);

      /* 'assignment expression' production can't be continued with an operator,
       *  so just propagating it to 'expression' production */
      state_p->is_completed = false;
      state_p->state = JSP_STATE_EXPR_EXPRESSION;
    }
    else if (state_p->state == JSP_STATE_EXPR_CONDITION)
    {
      JERRY_ASSERT (!state_p->is_completed);
      JERRY_ASSERT (is_subexpr_end);

      /* ECMA-262 v5, 11.12 */
      if (state_p->token_type == TOK_QUERY)
      {
        current_token_must_be (TOK_COLON);
        skip_token ();

        JERRY_ASSERT (state_p->is_fixed_ret_operand);
        JERRY_ASSERT (state_p->operand.is_register_operand ());
        JERRY_ASSERT (subexpr_type == JSP_STATE_EXPR_ASSIGNMENT);

        subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);

        dump_variable_assignment (state_p->operand, subexpr_operand);

        dump_jump_to_end_for_rewrite ();
        rewrite_conditional_check ();

        state_p->token_type = TOK_COLON;

        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, in_allowed);
      }
      else
      {
        JERRY_ASSERT (state_p->token_type == TOK_COLON);

        JERRY_ASSERT (state_p->is_fixed_ret_operand);
        JERRY_ASSERT (state_p->operand.is_register_operand ());
        JERRY_ASSERT (subexpr_type == JSP_STATE_EXPR_ASSIGNMENT);

        subexpr_operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_operand);

        dump_variable_assignment (state_p->operand, subexpr_operand);
        rewrite_jump_to_end ();

        state_p->token_type = TOK_EMPTY;
        state_p->is_fixed_ret_operand = false;

        state_p->state = JSP_STATE_EXPR_ASSIGNMENT;
        state_p->is_completed = true;
      }
    }
    else
    {
      /* ECMA-262 v5, 11.14 */
      JERRY_ASSERT (state_p->state == JSP_STATE_EXPR_EXPRESSION);

      if (is_subexpr_end)
      {
        JERRY_ASSERT (state_p->token_type == TOK_COMMA);

        /*
         * The operand should be already evaluated
         *
         * See also:
         *          11.14, step 2
         */
        JERRY_ASSERT (state_p->operand.is_register_operand ());

        if (!subexpr_operand.is_register_operand ())
        {
          /* evaluating, if reference */
          subexpr_operand = dump_assignment_of_lhs_if_reference (subexpr_operand);
        }

        state_p->operand = subexpr_operand;
      }
      else
      {
        JERRY_ASSERT (!state_p->is_completed);

        if (token_is (TOK_COMMA))
        {
          skip_token ();

          JERRY_ASSERT (!token_is (TOK_COMMA));

          state_p->token_type = TOK_COMMA;

          /* ECMA-262 v5, 11.14, step 2 */
          state_p->operand = dump_assignment_of_lhs_if_reference (state_p->operand);

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, in_allowed);
        }
        else
        {
          state_p->is_completed = true;
        }
      }
    }
  }

  return empty_operand ();
} /* parse_expression_ */

/**
 * Parse an expression
 *
 * expression
 *  : assignment_expression (LT!* ',' LT!* assignment_expression)*
 *  ;
 *
 * @return jsp_operand_t which holds result of expression
 */
static jsp_operand_t
parse_expression (bool in_allowed, /**< flag indicating if 'in' is allowed inside expression to parse */
                  jsp_eval_ret_store_t dump_eval_ret_store) /**< flag indicating if 'eval'
                                                             *   result code store should be dumped */
{
  jsp_operand_t expr = parse_expression_ (JSP_STATE_EXPR_EXPRESSION, in_allowed);

  if (serializer_get_scope ()->type == SCOPE_TYPE_EVAL
      && dump_eval_ret_store == JSP_EVAL_RET_STORE_DUMP)
  {
    expr = dump_assignment_of_lhs_if_value_based_reference (expr);

    dump_variable_assignment (eval_ret_operand (), expr);
  }

  return expr;
} /* parse_expression */

/* variable_declaration
  : Identifier LT!* initialiser?
  ;
   initialiser
  : '=' LT!* assignment_expression
  ; */
static jsp_operand_t
parse_variable_declaration (void)
{
  current_token_must_be (TOK_NAME);

  const lit_cpointer_t lit_cp = token_data_as_lit_cp ();
  const jsp_operand_t name = literal_operand (lit_cp);

  if (!scopes_tree_variable_declaration_exists (serializer_get_scope (), lit_cp))
  {
    jsp_early_error_check_for_eval_and_arguments_in_strict_mode (name, is_strict_mode (), tok.loc);

    dump_variable_declaration (lit_cp);
  }

  skip_token ();

  if (token_is (TOK_EQ))
  {
    skip_token ();
    const jsp_operand_t expr = parse_expression_ (JSP_STATE_EXPR_ASSIGNMENT, true);

    dump_variable_assignment (name, dump_assignment_of_lhs_if_value_based_reference (expr));
  }

  return name;
} /* parse_variable_declaration */

static jsp_operand_t
parse_expression_inside_parens (void)
{
  current_token_must_be (TOK_OPEN_PAREN);
  skip_token ();

  const jsp_operand_t res = parse_expression (true, JSP_EVAL_RET_STORE_NOT_DUMP);

  current_token_must_be (TOK_CLOSE_PAREN);

  return res;
}

static void
parse_expression_inside_parens_begin (void)
{
  current_token_must_be (TOK_OPEN_PAREN);
  skip_token ();
}

static void
parse_expression_inside_parens_end (void)
{
  current_token_must_be (TOK_CLOSE_PAREN);
  skip_token ();
}

static void
jsp_start_statement_parse (jsp_state_expr_t stat)
{
  jsp_state_t new_state;

  new_state.state = stat;
  new_state.req_expr_type = JSP_STATE_STAT_STATEMENT;
  new_state.operand = empty_operand ();
  new_state.token_type = TOK_EMPTY;
  new_state.u.statement.outermost_stmt_label_p = NULL;

  new_state.is_completed = false;
  new_state.is_list_in_process = false;
  new_state.is_no_in_mode = false;
  new_state.is_fixed_ret_operand = false;
  new_state.is_complex_production = false;
  new_state.is_rewrite_chain_active = false;
  new_state.is_raised = false;
  new_state.var_decl = false;
  new_state.is_default_branch = false;

  jsp_state_push (new_state);
} /* jsp_start_statement_parse */

static void
insert_semicolon (void)
{
  bool is_new_line_occured = lexer_is_preceded_by_newlines (tok);
  bool is_close_brace_or_eof = (token_is (TOK_CLOSE_BRACE) || token_is (TOK_EOF));

  if (!is_new_line_occured && !is_close_brace_or_eof)
  {
    if (token_is (TOK_SEMICOLON))
    {
      skip_token ();
    }
    else if (!token_is (TOK_EOF))
    {
      EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Expected either ';' or newline token");
    }
  }
}


#define JSP_COMPLETE_STATEMENT_PARSE() \
do \
{ \
  state_p->state = JSP_STATE_STAT_STATEMENT; \
  state_p->is_completed = true; \
  dumper_new_statement (); \
} \
while (0)

#define JSP_PUSH_STATE_AND_STATEMENT_PARSE(s) \
do \
{ \
  state_p->state = (s); \
  jsp_start_statement_parse (JSP_STATE_STAT_EMPTY); \
  dumper_new_statement (); \
} \
while (0)

/**
 * Parse statement
 */
static void
parse_statement_ (void)
{
  dumper_new_scope ();

  dumper_new_statement ();

  jsp_start_statement_parse (JSP_STATE_SOURCE_ELEMENTS_INIT);
  uint32_t start_pos = jsp_state_stack_pos;
  bool in_allowed = true;

  while (true)
  {
    bool is_subexpr_end = false;
    jsp_operand_t subexpr_operand;

    jsp_state_t *state_p = jsp_state_top ();

    if (state_p->state == state_p->req_expr_type && state_p->is_completed)
    {
      (void) jsp_is_stack_empty ();

      if (start_pos == jsp_state_stack_pos) // FIXME: jsp_is_stack_empty ()
      {
        jsp_state_pop ();
        dumper_finish_scope ();
        break;
      }
      else
      {
        is_subexpr_end = (state_p->req_expr_type != JSP_STATE_STAT_STATEMENT);

        subexpr_operand = state_p->operand;

        jsp_state_pop ();
        state_p = jsp_state_top ();
      }
    }

    if (state_p->state == JSP_STATE_SOURCE_ELEMENTS_INIT)
    {
      scope_type_t scope_type = serializer_get_scope ()->type;

      state_p->u.source_elements.prev_label_set_p = jsp_label_new_set ();

      dumper_new_scope ();

      state_p->u.source_elements.scope_code_flags_oc = dump_scope_code_flags_for_rewrite ();
      state_p->u.source_elements.reg_var_decl_oc = dump_reg_var_decl_for_rewrite ();

      if (scope_type == SCOPE_TYPE_EVAL)
      {
        dump_undefined_assignment (eval_ret_operand ());
      }

      state_p->state = JSP_STATE_SOURCE_ELEMENTS;
    }
    else if (state_p->state == JSP_STATE_SOURCE_ELEMENTS)
    {
      scope_type_t scope_type = serializer_get_scope ()->type;

      jsp_token_type_t end_token_type = (scope_type == SCOPE_TYPE_FUNCTION) ? TOK_CLOSE_BRACE : TOK_EOF;

      if (token_is (end_token_type))
      {
        opcode_scope_code_flags_t scope_flags = OPCODE_SCOPE_CODE_FLAGS__EMPTY;

        scopes_tree fe_scope_tree = serializer_get_scope ();
        if (fe_scope_tree->strict_mode)
        {
          scope_flags = (opcode_scope_code_flags_t) (scope_flags | OPCODE_SCOPE_CODE_FLAGS_STRICT);
        }

        if (!fe_scope_tree->ref_arguments)
        {
          scope_flags = (opcode_scope_code_flags_t) (scope_flags | OPCODE_SCOPE_CODE_FLAGS_NOT_REF_ARGUMENTS_IDENTIFIER);
        }

        if (!fe_scope_tree->ref_eval)
        {
          scope_flags = (opcode_scope_code_flags_t) (scope_flags | OPCODE_SCOPE_CODE_FLAGS_NOT_REF_EVAL_IDENTIFIER);
        }

#ifdef CONFIG_PARSER_ENABLE_PARSE_TIME_BYTE_CODE_OPTIMIZER
        vm_instr_counter_t number_of_instrs_removed_from_function_header;

        scope_flags = jsp_try_move_vars_to_regs (scope_flags, &number_of_instrs_removed_from_function_header);

        JERRY_ASSERT (state_p->u.source_elements.scope_code_flags_oc >= number_of_instrs_removed_from_function_header);
        JERRY_ASSERT (state_p->u.source_elements.reg_var_decl_oc >= number_of_instrs_removed_from_function_header);

        vm_instr_counter_t new_oc;

        new_oc = state_p->u.source_elements.scope_code_flags_oc;
        new_oc = (vm_instr_counter_t) (new_oc - number_of_instrs_removed_from_function_header);
        state_p->u.source_elements.scope_code_flags_oc = new_oc;

        new_oc = state_p->u.source_elements.reg_var_decl_oc;
        new_oc = (vm_instr_counter_t) (new_oc - number_of_instrs_removed_from_function_header);
        state_p->u.source_elements.reg_var_decl_oc = new_oc;
#endif /* CONFIG_PARSER_ENABLE_PARSE_TIME_BYTE_CODE_OPTIMIZER */

        rewrite_scope_code_flags (state_p->u.source_elements.scope_code_flags_oc, scope_flags);
        rewrite_reg_var_decl (state_p->u.source_elements.reg_var_decl_oc);

        jsp_label_restore_previous_set (state_p->u.source_elements.prev_label_set_p);

        JSP_COMPLETE_STATEMENT_PARSE ();

        dumper_finish_scope ();
      }
      else
      {
        if (!token_is (TOK_KW_FUNCTION)) // FIXME: Remove
        {
          JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_SOURCE_ELEMENTS_WAIT_STATEMENT);
        }
        else
        {
          JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_SOURCE_ELEMENTS);
        }
      }
    }
    else if (state_p->state == JSP_STATE_SOURCE_ELEMENTS_WAIT_STATEMENT)
    {
      state_p->state = JSP_STATE_SOURCE_ELEMENTS;
    }
    else if (state_p->state == JSP_STATE_EXPR_EMPTY)
    {
      state_p->operand = parse_expression (!state_p->is_no_in_mode, JSP_EVAL_RET_STORE_NOT_DUMP);
      state_p->state = JSP_STATE_EXPR_EXPRESSION;
      state_p->is_completed = true;
    }
    else if (state_p->state == JSP_STATE_STAT_EMPTY)
    {
      dumper_new_statement ();

      if (token_is (TOK_KW_IF)) /* IfStatement */
      {
        skip_token ();

        parse_expression_inside_parens_begin ();

        state_p->state = JSP_STATE_STAT_IF_BRANCH_START;

        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, in_allowed);
      }
      else if (token_is (TOK_OPEN_BRACE))
      {
        skip_token ();

        state_p->state = JSP_STATE_STAT_BLOCK;
        jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT_LIST);
      }
      else if (token_is (TOK_KW_VAR))
      {
        state_p->state = JSP_STATE_STAT_VAR_DECL;
        state_p->var_decl = true;
      }
      else if (token_is (TOK_KW_DO)
               || token_is (TOK_KW_WHILE)
               || token_is (TOK_KW_FOR))
      {
        jsp_label_push (&state_p->u.statement.label,
                        (jsp_label_type_flag_t) (JSP_LABEL_TYPE_UNNAMED_BREAKS | JSP_LABEL_TYPE_UNNAMED_CONTINUES),
                        NOT_A_LITERAL);

        state_p->u.statement.outermost_stmt_label_p = (state_p->u.statement.outermost_stmt_label_p != NULL
                                                      ? state_p->u.statement.outermost_stmt_label_p
                                                      : &state_p->u.statement.label);

        if (token_is (TOK_KW_DO))
        {
          dumper_set_next_iteration_target ();
          skip_token ();

          JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_STAT_DO_WHILE);
        }
        else if (token_is (TOK_KW_WHILE))
        {
          skip_token ();
          current_token_must_be (TOK_OPEN_PAREN);
          state_p->u.statement.loc[0] = tok.loc;
          jsp_skip_braces (TOK_OPEN_PAREN);

          dump_jump_to_end_for_rewrite ();

          dumper_set_next_iteration_target ();

          skip_token ();

          JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_STAT_WHILE);
        }
        else
        {
          assert_keyword (TOK_KW_FOR);

          skip_token ();
          current_token_must_be (TOK_OPEN_PAREN);

          locus for_open_paren_loc, for_body_statement_loc;

          for_open_paren_loc = tok.loc;

          jsp_skip_braces (TOK_OPEN_PAREN);
          skip_token ();

          for_body_statement_loc = tok.loc;

          lexer_seek (for_open_paren_loc);
          tok = lexer_next_token (false);

          bool is_plain_for = jsp_find_next_token_before_the_locus (TOK_SEMICOLON,
                                                                    for_body_statement_loc,
                                                                    true);
          lexer_seek (for_open_paren_loc);
          tok = lexer_next_token (false);

          state_p->u.statement.loc[0] = for_body_statement_loc;

          if (is_plain_for)
          {
            current_token_must_be (TOK_OPEN_PAREN);
            skip_token ();

            // Initializer
            if (token_is (TOK_KW_VAR))
            {
              state_p->state = JSP_STATE_STAT_FOR_INIT_END;
              jsp_start_statement_parse (JSP_STATE_STAT_VAR_DECL);
            }
            else
            {
              if (!token_is (TOK_SEMICOLON))
              {
                jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, false);
              }
              else
              {
                // Initializer is empty
              }
              state_p->state = JSP_STATE_STAT_FOR_INIT_END;
            }
          }
          else
          {
            if (jsp_label_raise_nested_jumpable_border ())
            {
              state_p->is_raised = true;
            }

            current_token_must_be (TOK_OPEN_PAREN);
            skip_token ();

            // Save Iterator location
            locus iterator_loc = tok.loc;

            while (lit_utf8_iterator_pos_cmp (tok.loc, for_body_statement_loc) < 0)
            {
              if (jsp_find_next_token_before_the_locus (TOK_KW_IN,
                                                        for_body_statement_loc,
                                                        true))
              {
                break;
              }
              else
              {
                EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Invalid for statement");
              }
            }

            JERRY_ASSERT (token_is (TOK_KW_IN));
            skip_token ();

            // Collection
            jsp_operand_t collection = parse_expression (true, JSP_EVAL_RET_STORE_NOT_DUMP);
            // TODO: add state for expression parsing
            current_token_must_be (TOK_CLOSE_PAREN);
            skip_token ();

            // Dump for-in instruction
            collection = dump_assignment_of_lhs_if_value_based_reference (collection);
            state_p->u.for_in.header_pos = dump_for_in_for_rewrite (collection); /**< for in pos */

            // Dump assignment VariableDeclarationNoIn / LeftHandSideExpression <- VM_REG_SPECIAL_FOR_IN_PROPERTY_NAME
            lexer_seek (iterator_loc);
            tok = lexer_next_token (false);

            jsp_operand_t iterator, for_in_special_reg;
            for_in_special_reg = jsp_create_operand_for_in_special_reg ();

            if (token_is (TOK_KW_VAR))
            {
              skip_token ();

              jsp_operand_t name = parse_variable_declaration ();
              JERRY_ASSERT (name.is_literal_operand ());

              iterator = jsp_operand_t::make_identifier_operand (name.get_literal ());
            }
            else
            {
              iterator = parse_expression_ (JSP_STATE_EXPR_LEFTHANDSIDE, true);
              // TODO: add state for expression parsing
            }

            if (iterator.is_value_based_reference_operand ())
            {
              dump_prop_setter (iterator, for_in_special_reg);
            }
            else
            {
              dump_variable_assignment (iterator, for_in_special_reg);
            }

            // Body
            lexer_seek (for_body_statement_loc);
            tok = lexer_next_token (false);

            JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_STAT_FOR_IN_FINISH);
          }
        }
      }
      else if (token_is (TOK_NAME))  // LabelledStatement or ExpressionStatement
      {
        const token temp = tok;
        skip_token ();
        if (token_is (TOK_COLON))
        {
          skip_token ();

          lit_cpointer_t name_cp;
          name_cp.packed_value = temp.uid;

          jsp_label_t *label_p = jsp_label_find (JSP_LABEL_TYPE_NAMED, name_cp, NULL);
          if (label_p != NULL)
          {
            EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Label is duplicated");
          }

          jsp_label_push (&state_p->u.statement.label, JSP_LABEL_TYPE_NAMED, name_cp);

          state_p->u.statement.outermost_stmt_label_p = (state_p->u.statement.outermost_stmt_label_p != NULL
                                                         ? state_p->u.statement.outermost_stmt_label_p
                                                         : &state_p->u.statement.label);

          state_p->state = JSP_STATE_STAT_ITER_FINISH;
          jsp_start_statement_parse (JSP_STATE_STAT_EMPTY);
          jsp_state_top ()->u.statement.outermost_stmt_label_p = state_p->u.statement.outermost_stmt_label_p;
        }
        else
        {
          lexer_seek (temp.loc);
          skip_token ();
          jsp_operand_t expr = parse_expression (true, JSP_EVAL_RET_STORE_DUMP);
          dump_assignment_of_lhs_if_reference (expr);
          insert_semicolon ();

          JSP_COMPLETE_STATEMENT_PARSE ();
        }
      }
      else if (token_is (TOK_KW_SWITCH))
      {
        skip_token ();

        const jsp_operand_t switch_expr = parse_expression_inside_parens ();
        skip_token ();

        current_token_must_be (TOK_OPEN_BRACE);

        start_dumping_case_clauses ();
        const locus start_loc = tok.loc;
        bool was_default = false;
        size_t default_body_index = 0;
        array_list body_locs = array_list_init (sizeof (locus));

        // First, generate table of jumps
        skip_token ();
        while (token_is (TOK_KW_CASE) || token_is (TOK_KW_DEFAULT))
        {
          if (token_is (TOK_KW_CASE))
          {
            skip_token ();
            jsp_operand_t case_expr = parse_expression (true, JSP_EVAL_RET_STORE_NOT_DUMP);
            case_expr = dump_assignment_of_lhs_if_value_based_reference (case_expr);

            current_token_must_be (TOK_COLON);

            dump_case_clause_check_for_rewrite (switch_expr, case_expr);
            skip_token ();
            body_locs = array_list_append (body_locs, (void*) &tok.loc);
            skip_case_clause_body ();
          }
          else if (token_is (TOK_KW_DEFAULT))
          {
            if (was_default)
            {
              EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Duplication of 'default' clause");
            }
            was_default = true;

            skip_token ();
            current_token_must_be (TOK_COLON);
            skip_token ();

            default_body_index = array_list_len (body_locs);
            body_locs = array_list_append (body_locs, (void*) &tok.loc);
            skip_case_clause_body ();
          }
        }
        current_token_must_be (TOK_CLOSE_BRACE);

        dump_default_clause_check_for_rewrite ();

        lexer_seek (start_loc);

        skip_token ();
        current_token_must_be (TOK_OPEN_BRACE);

        jsp_label_push (&state_p->u.statement.label,
                        JSP_LABEL_TYPE_UNNAMED_BREAKS,
                        NOT_A_LITERAL);

        // Second, parse case clauses' bodies and rewrite jumps
        skip_token ();

        if (array_list_len (body_locs) > 0)
        {
          for (size_t i = array_list_len (body_locs); i > 0; i--)
          {
            jsp_start_statement_parse (JSP_STATE_STAT_SWITCH_BRANCH);
            jsp_state_top ()->u.statement.loc[0] = * (locus *) array_list_element (body_locs, i - 1);

            if (was_default && default_body_index == i - 1)
            {
              jsp_state_top ()->is_default_branch = true;
            }
          }
        }

        array_list_free (body_locs);
        state_p->state = JSP_STATE_STAT_SWITCH_FINISH;
        state_p->is_default_branch = was_default;
      }
      else if (token_is (TOK_SEMICOLON))
      {
        skip_token ();

        JSP_COMPLETE_STATEMENT_PARSE ();
      }
      else if (token_is (TOK_KW_CONTINUE)
               || token_is (TOK_KW_BREAK))
      {
        bool is_break = token_is (TOK_KW_BREAK);

        skip_token ();

        jsp_label_t *label_p;
        bool is_simply_jumpable = true;
        if (!lexer_is_preceded_by_newlines (tok)
            && token_is (TOK_NAME))
        {
          /* break or continue on a label */
          label_p = jsp_label_find (JSP_LABEL_TYPE_NAMED, token_data_as_lit_cp (), &is_simply_jumpable);

          if (label_p == NULL)
          {
            EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Label not found");
          }

          skip_token ();
        }
        else if (is_break)
        {
          label_p = jsp_label_find (JSP_LABEL_TYPE_UNNAMED_BREAKS,
                                    NOT_A_LITERAL,
                                    &is_simply_jumpable);

          if (label_p == NULL)
          {
            EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "No corresponding statement for the break");
          }
        }
        else
        {
          JERRY_ASSERT (!is_break);

          label_p = jsp_label_find (JSP_LABEL_TYPE_UNNAMED_CONTINUES,
                                    NOT_A_LITERAL,
                                    &is_simply_jumpable);

          if (label_p == NULL)
          {
            EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "No corresponding statement for the continue");
          }
        }

        insert_semicolon ();

        JERRY_ASSERT (label_p != NULL);

        jsp_label_add_jump (label_p, is_simply_jumpable, is_break);

        JSP_COMPLETE_STATEMENT_PARSE ();
      }
      else if (token_is (TOK_KW_RETURN))
      {
        if (serializer_get_scope ()->type != SCOPE_TYPE_FUNCTION)
        {
          EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Return is illegal");
        }

        skip_token ();

        if (!token_is (TOK_SEMICOLON)
            && !lexer_is_preceded_by_newlines (tok)
            && !token_is (TOK_CLOSE_BRACE))
        {
          const jsp_operand_t op = parse_expression (true, JSP_EVAL_RET_STORE_NOT_DUMP);

          dump_retval (dump_assignment_of_lhs_if_value_based_reference (op));

          insert_semicolon ();
        }
        else
        {
          dump_ret ();
        }

        JSP_COMPLETE_STATEMENT_PARSE ();
      }
      else if (token_is (TOK_KW_TRY))
      {
        skip_token ();

        scopes_tree_set_contains_try (serializer_get_scope ());

        state_p->is_raised = jsp_label_raise_nested_jumpable_border ();

        dump_try_for_rewrite ();

        current_token_must_be (TOK_OPEN_BRACE);
        skip_token ();

        state_p->state = JSP_STATE_STAT_TRY;
        jsp_start_statement_parse (JSP_STATE_STAT_BLOCK);
        jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT_LIST);
      }
      else if (token_is (TOK_KW_WITH))
      {
        skip_token ();

        if (is_strict_mode ())
        {
          EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "'with' expression is not allowed in strict mode.");
        }

        const jsp_operand_t expr = parse_expression_inside_parens ();

        scopes_tree_set_contains_with (serializer_get_scope ());

        state_p->is_raised = jsp_label_raise_nested_jumpable_border ();

        state_p->u.rewrite_chain = dump_with_for_rewrite (expr);
        skip_token ();

        JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_STAT_WITH_FINISH);
      }
      else if (token_is (TOK_KW_THROW))
      {
        skip_token ();
        const jsp_operand_t op = parse_expression (true, JSP_EVAL_RET_STORE_NOT_DUMP);
        insert_semicolon ();
        dump_throw (dump_assignment_of_lhs_if_value_based_reference (op));

        JSP_COMPLETE_STATEMENT_PARSE ();
      }
      else if (token_is (TOK_KW_FUNCTION))
      {
        skip_token ();

        current_token_must_be (TOK_NAME);

        const jsp_operand_t func_name = literal_operand (token_data_as_lit_cp ());
        skip_token ();

        jsp_start_parse_function_scope (func_name, false, NULL);

        state_p->state = JSP_STATE_FUNC_DECL_FINISH;
        jsp_start_statement_parse (JSP_STATE_SOURCE_ELEMENTS_INIT);
      }
      else
      {
        parse_expression (true, JSP_EVAL_RET_STORE_DUMP);
        insert_semicolon ();

        JSP_COMPLETE_STATEMENT_PARSE ();
      }
    }
    else if (state_p->state == JSP_STATE_STAT_BLOCK)
    {
      current_token_must_be (TOK_CLOSE_BRACE);
      skip_token ();

      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else if (state_p->state == JSP_STATE_STAT_IF_BRANCH_START)
    {
      if (is_subexpr_end) // Finished parsing condition
      {
        parse_expression_inside_parens_end ();

        jsp_operand_t cond = subexpr_operand;

        cond = dump_assignment_of_lhs_if_value_based_reference (cond);
        dump_conditional_check_for_rewrite (cond);

        JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_STAT_IF_BRANCH_START);
      }
      else
      {
        if (token_is (TOK_KW_ELSE))
        {
          skip_token ();

          dump_jump_to_end_for_rewrite ();
          rewrite_conditional_check ();

          JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_STAT_IF_BRANCH_END);
        }
        else
        {
          rewrite_conditional_check ();

          JSP_COMPLETE_STATEMENT_PARSE ();
        }
      }
    }
    else if (state_p->state == JSP_STATE_STAT_IF_BRANCH_END)
    {
      rewrite_jump_to_end ();

      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else if (state_p->state == JSP_STATE_STAT_STATEMENT_LIST)
    {
      while (token_is (TOK_SEMICOLON))
      {
        skip_token ();
      }

      if (token_is (TOK_CLOSE_BRACE)
          || (token_is (TOK_KW_CASE) || token_is (TOK_KW_DEFAULT)))
      {
        JSP_COMPLETE_STATEMENT_PARSE ();
      }
      else
      {
        jsp_start_statement_parse (JSP_STATE_STAT_EMPTY);
      }
    }
    else if (state_p->state == JSP_STATE_STAT_VAR_DECL)
    {
      skip_token ();

      current_token_must_be (TOK_NAME);

      const lit_cpointer_t lit_cp = token_data_as_lit_cp ();
      const jsp_operand_t name = literal_operand (lit_cp);

      if (!scopes_tree_variable_declaration_exists (serializer_get_scope (), lit_cp))
      {
        jsp_early_error_check_for_eval_and_arguments_in_strict_mode (name, is_strict_mode (), tok.loc);

        dump_variable_declaration (lit_cp);
      }

      skip_token ();

      if (token_is (TOK_EQ))
      {
        skip_token ();
        const jsp_operand_t expr = parse_expression_ (JSP_STATE_EXPR_ASSIGNMENT, true);

        dump_variable_assignment (name, dump_assignment_of_lhs_if_value_based_reference (expr));
      }

      if (!token_is (TOK_COMMA))
      {
        JSP_COMPLETE_STATEMENT_PARSE ();

        if (state_p->var_decl)
        {
          insert_semicolon ();
        }
      }
    }
    else if (state_p->state == JSP_STATE_STAT_DO_WHILE)
    {
      if (is_subexpr_end)
      {
        parse_expression_inside_parens_end ();

        const jsp_operand_t cond = subexpr_operand;
        dump_continue_iterations_check (cond);

        state_p->state = JSP_STATE_STAT_ITER_FINISH;
      }
      else
      {
        assert_keyword (TOK_KW_WHILE);
        skip_token ();

        jsp_label_setup_continue_target (state_p->u.statement.outermost_stmt_label_p,
                                         serializer_get_current_instr_counter ());

        parse_expression_inside_parens_begin ();
        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
      }
    }
    else if (state_p->state == JSP_STATE_STAT_WHILE)
    {
      if (is_subexpr_end)
      {
        parse_expression_inside_parens_end ();

        const jsp_operand_t cond = subexpr_operand;
        dump_continue_iterations_check (cond);

        lexer_seek (state_p->u.statement.loc[0]);
        skip_token ();

        state_p->state = JSP_STATE_STAT_ITER_FINISH;
      }
      else
      {
        jsp_label_setup_continue_target (state_p->u.statement.outermost_stmt_label_p,
                                         serializer_get_current_instr_counter ());

        rewrite_jump_to_end ();

        const locus end_loc = tok.loc;

        lexer_seek (state_p->u.statement.loc[0]);
        skip_token ();

        state_p->u.statement.loc[0] = end_loc;

        parse_expression_inside_parens_begin ();
        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
      }
    }
    else if (state_p->state == JSP_STATE_STAT_FOR_INIT_END)
    {
      // Jump -> ConditionCheck
      dump_jump_to_end_for_rewrite ();

      dumper_set_next_iteration_target ();

      current_token_must_be (TOK_SEMICOLON);
      skip_token ();

      locus for_body_statement_loc = state_p->u.statement.loc[0];
      // Save Condition locus
      state_p->u.statement.loc[0] = tok.loc;

      if (!jsp_find_next_token_before_the_locus (TOK_SEMICOLON,
                                                 for_body_statement_loc,
                                                 true))
      {
        EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Invalid for statement");
      }

      current_token_must_be (TOK_SEMICOLON);
      skip_token ();

      // Save Increment locus
      state_p->u.statement.loc[1] = tok.loc;

      // Body
      lexer_seek (for_body_statement_loc);
      skip_token ();

      JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_STAT_FOR_INCREMENT);
    }
    else if (state_p->state == JSP_STATE_STAT_FOR_INCREMENT)
    {
      if (is_subexpr_end)
      {
        state_p->state = JSP_STATE_STAT_FOR_COND;
      }
      else
      {
        // Save LoopEnd locus
        const locus loop_end_loc = tok.loc;

        // Setup ContinueTarget
        jsp_label_setup_continue_target (state_p->u.statement.outermost_stmt_label_p,
                                         serializer_get_current_instr_counter ());

        // Increment
        lexer_seek (state_p->u.statement.loc[1]);
        state_p->u.statement.loc[1] = loop_end_loc;
        skip_token ();

        if (!token_is (TOK_CLOSE_PAREN))
        {
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
        }
        else
        {
          state_p->state = JSP_STATE_STAT_FOR_COND;
        }
      }
    }
    else if (state_p->state == JSP_STATE_STAT_FOR_COND)
    {
      if (is_subexpr_end)
      {
          jsp_operand_t cond = subexpr_operand;
          // TODO: add state for expression parsing
          dump_continue_iterations_check (cond);

          state_p->state = JSP_STATE_STAT_FOR_FINISH;
      }
      else
      {
        current_token_must_be (TOK_CLOSE_PAREN);

        // Setup ConditionCheck
        rewrite_jump_to_end ();

        // Condition
        lexer_seek (state_p->u.statement.loc[0]);
        skip_token ();

        if (token_is (TOK_SEMICOLON))
        {
          dump_continue_iterations_check (empty_operand ());
          state_p->state = JSP_STATE_STAT_FOR_FINISH;
        }
        else
        {
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
        }
      }
    }
    else if (state_p->state == JSP_STATE_STAT_FOR_FINISH)
    {
      lexer_seek (state_p->u.statement.loc[1]);
      skip_token ();

      state_p->state = JSP_STATE_STAT_ITER_FINISH;
    }
    else if (state_p->state == JSP_STATE_STAT_FOR_IN_FINISH)
    {
      // Save LoopEnd locus
      const locus loop_end_loc = tok.loc;

      // Setup ContinueTarget
      jsp_label_setup_continue_target (state_p->u.statement.outermost_stmt_label_p,
                                       serializer_get_current_instr_counter ());

      // Write position of for-in end to for_in instruction
      rewrite_for_in (state_p->u.for_in.header_pos);

      // Dump meta (OPCODE_META_TYPE_END_FOR_IN)
      dump_for_in_end ();

      lexer_seek (loop_end_loc);
      tok = lexer_next_token (false);

      if (state_p->is_raised)
      {
        jsp_label_remove_nested_jumpable_border ();
      }

      state_p->state = JSP_STATE_STAT_ITER_FINISH;
    }
    else if (state_p->state == JSP_STATE_STAT_ITER_FINISH)
    {
      JSP_COMPLETE_STATEMENT_PARSE ();

      jsp_label_rewrite_jumps_and_pop (&state_p->u.statement.label,
                                       serializer_get_current_instr_counter ());
    }
    else if (state_p->state == JSP_STATE_STAT_SWITCH_BRANCH)
    {
      lexer_seek (state_p->u.statement.loc[0]);
      skip_token ();

      if (state_p->is_default_branch)
      {
        rewrite_default_clause ();
        if (token_is (TOK_KW_CASE))
        {
          JSP_COMPLETE_STATEMENT_PARSE ();
          continue;
        }
      }
      else
      {
        rewrite_case_clause ();
        if (token_is (TOK_KW_CASE) || token_is (TOK_KW_DEFAULT))
        {
          JSP_COMPLETE_STATEMENT_PARSE ();
          continue;
        }
      }

      JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_STAT_STATEMENT_LIST);
    }
    else if (state_p->state == JSP_STATE_STAT_SWITCH_FINISH)
    {
      if (!state_p->is_default_branch)
      {
        rewrite_default_clause ();
      }

      current_token_must_be (TOK_CLOSE_BRACE);
      skip_token ();

      jsp_label_rewrite_jumps_and_pop (&state_p->u.statement.label,
                                       serializer_get_current_instr_counter ());

      finish_dumping_case_clauses ();

      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else if (state_p->state == JSP_STATE_STAT_TRY)
    {
      rewrite_try ();

      if (!token_is (TOK_KW_CATCH)
          && !token_is (TOK_KW_FINALLY))
      {
        EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Expected either 'catch' or 'finally' token");
      }

      if (token_is (TOK_KW_CATCH))
      {
        skip_token ();

        current_token_must_be (TOK_OPEN_PAREN);
        skip_token ();

        current_token_must_be (TOK_NAME);

        const jsp_operand_t exception = literal_operand (token_data_as_lit_cp ());
        jsp_early_error_check_for_eval_and_arguments_in_strict_mode (exception, is_strict_mode (), tok.loc);

        skip_token ();

        current_token_must_be (TOK_CLOSE_PAREN);
        skip_token ();

        dump_catch_for_rewrite (exception);

        current_token_must_be (TOK_OPEN_BRACE);
        skip_token ();

        state_p->state = JSP_STATE_STAT_CATCH_FINISH;

        jsp_start_statement_parse (JSP_STATE_STAT_BLOCK);
        jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT_LIST);
      }
      else
      {
        JERRY_ASSERT (token_is (TOK_KW_FINALLY));
        skip_token ();

        dump_finally_for_rewrite ();

        current_token_must_be (TOK_OPEN_BRACE);
        skip_token ();

        state_p->state = JSP_STATE_STAT_FINALLY_FINISH;

        jsp_start_statement_parse (JSP_STATE_STAT_BLOCK);
        jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT_LIST);
      }
    }
    else if (state_p->state == JSP_STATE_STAT_CATCH_FINISH)
    {
      rewrite_catch ();

      if (token_is (TOK_KW_FINALLY))
      {
        skip_token ();
        dump_finally_for_rewrite ();

        current_token_must_be (TOK_OPEN_BRACE);
        skip_token ();

        state_p->state = JSP_STATE_STAT_FINALLY_FINISH;

        jsp_start_statement_parse (JSP_STATE_STAT_BLOCK);
        jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT_LIST);
      }
      else
      {
        state_p->state = JSP_STATE_STAT_TRY_FINISH;
      }
    }
    else if (state_p->state == JSP_STATE_STAT_FINALLY_FINISH)
    {
      rewrite_finally ();

      state_p->state = JSP_STATE_STAT_TRY_FINISH;
    }
    else if (state_p->state == JSP_STATE_STAT_TRY_FINISH)
    {
      dump_end_try_catch_finally ();

      if (state_p->is_raised)
      {
        jsp_label_remove_nested_jumpable_border ();
      }

      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else if (state_p->state == JSP_STATE_STAT_WITH_FINISH)
    {
      rewrite_with (state_p->u.rewrite_chain);
      dump_with_end ();

      if (state_p->is_raised)
      {
        jsp_label_remove_nested_jumpable_border ();
      }

      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else if (state_p->state == JSP_STATE_FUNC_DECL_FINISH)
    {
      jsp_finish_parse_function_scope (false);
      JSP_COMPLETE_STATEMENT_PARSE ();
    }
  }
} /* parse_statement_ */

static void
skip_case_clause_body (void)
{
  while (!token_is (TOK_KW_CASE)
         && !token_is (TOK_KW_DEFAULT)
         && !token_is (TOK_CLOSE_BRACE))
  {
    if (token_is (TOK_OPEN_BRACE))
    {
      jsp_skip_braces (TOK_OPEN_BRACE);
    }
    skip_token ();
  }
}

/**
 * Parse program
 *
 * program
 *  : LT!* source_element_list LT!* EOF!
 *  ;
 *
 * @return true - if parse finished successfully (no SyntaxError was raised);
 *         false - otherwise.
 */
static jsp_status_t
parser_parse_program (const jerry_api_char_t *source_p, /**< source code buffer */
                      size_t source_size, /**< source code size in bytes */
                      bool in_eval, /**< flag indicating if we are parsing body of eval code */
                      bool is_strict, /**< flag, indicating whether current code
                                       *   inherited strict mode from code of an outer scope */
                      const bytecode_data_header_t **out_bytecode_data_p, /**< out: generated byte-code array
                                                                           *  (in case there were no syntax errors) */
                      bool *out_contains_functions_p) /**< out: optional (can be NULL, if the output is not needed)
                                                       *        flag, indicating whether the compiled byte-code
                                                       *        contains a function declaration / expression */
{
  JERRY_ASSERT (out_bytecode_data_p != NULL);

  const scope_type_t scope_type = (in_eval ? SCOPE_TYPE_EVAL : SCOPE_TYPE_GLOBAL);

#ifndef JERRY_NDEBUG
  volatile bool is_parse_finished = false;
#endif /* !JERRY_NDEBUG */

  jsp_status_t status;

  jsp_mm_init ();
  jsp_label_init ();

  serializer_set_show_instrs (parser_show_instrs);
  dumper_init ();
  jsp_early_error_init ();

  scopes_tree scope = scopes_tree_init (NULL, scope_type);
  serializer_set_scope (scope);
  scopes_tree_set_strict_mode (scope, is_strict);

  jmp_buf *jsp_early_error_label_p = jsp_early_error_get_early_error_longjmp_label ();
  int r = setjmp (*jsp_early_error_label_p);

  if (r == 0)
  {
    /*
     * Note:
     *      Operations that could raise an early error can be performed only during execution of the block.
     */

    lexer_init (source_p, source_size, parser_show_instrs);
    lexer_set_strict_mode (scopes_tree_strict_mode (scope));

    skip_token ();

    jsp_parse_directive_prologue ();

    parse_statement_ ();

    JERRY_ASSERT (token_is (TOK_EOF));

    if (scope_type == SCOPE_TYPE_EVAL)
    {
      dump_retval (eval_ret_operand ());
    }
    else
    {
      dump_ret ();
    }

#ifndef JERRY_NDEBUG
    is_parse_finished = true;
#endif /* !JERRY_NDEBUG */

    jsp_early_error_free ();

    *out_bytecode_data_p = serializer_merge_scopes_into_bytecode ();

    dumper_free ();

    if (out_contains_functions_p != NULL)
    {
      *out_contains_functions_p = scope->contains_functions;
    }

    serializer_set_scope (NULL);
    scopes_tree_free (scope);

    status = JSP_STATUS_OK;
  }
  else
  {
    /* SyntaxError handling */

#ifndef JERRY_NDEBUG
    JERRY_ASSERT (!is_parse_finished);
#endif /* !JERRY_NDEBUG */

    *out_bytecode_data_p = NULL;

    jsp_label_remove_all_labels ();
    jsp_mm_free_all ();

    jsp_early_error_t type = jsp_early_error_get_type ();

    if (type == JSP_EARLY_ERROR_SYNTAX)
    {
      status = JSP_STATUS_SYNTAX_ERROR;
    }
    else
    {
      JERRY_ASSERT (type == JSP_EARLY_ERROR_REFERENCE);

      status = JSP_STATUS_REFERENCE_ERROR;
    }
  }

  jsp_label_finalize ();
  jsp_mm_finalize ();

  return status;
} /* parser_parse_program */

/**
 * Parse source script
 *
 * @return true - if parse finished successfully (no SyntaxError were raised);
 *         false - otherwise.
 */
jsp_status_t
parser_parse_script (const jerry_api_char_t *source, /**< source script */
                     size_t source_size, /**< source script size it bytes */
                     const bytecode_data_header_t **out_bytecode_data_p) /**< out: generated byte-code array
                                                                          *  (in case there were no syntax errors) */
{
  return parser_parse_program (source, source_size, false, false, out_bytecode_data_p, NULL);
} /* parser_parse_script */

/**
 * Parse string passed to eval() call
 *
 * @return true - if parse finished successfully (no SyntaxError were raised);
 *         false - otherwise.
 */
jsp_status_t
parser_parse_eval (const jerry_api_char_t *source, /**< string passed to eval() */
                   size_t source_size, /**< string size in bytes */
                   bool is_strict, /**< flag, indicating whether eval is called
                                    *   from strict code in direct mode */
                   const bytecode_data_header_t **out_bytecode_data_p, /**< out: generated byte-code array
                                                                        *  (in case there were no syntax errors) */
                   bool *out_contains_functions_p) /**< out: flag, indicating whether the compiled byte-code
                                                    *        contains a function declaration / expression */
{
  JERRY_ASSERT (out_contains_functions_p != NULL);

  return parser_parse_program (source,
                               source_size,
                               true,
                               is_strict,
                               out_bytecode_data_p,
                               out_contains_functions_p);
} /* parser_parse_eval */

/**
 * Tell parser whether to dump bytecode
 */
void
parser_set_show_instrs (bool show_instrs) /**< flag indicating whether to dump bytecode */
{
  parser_show_instrs = show_instrs;
} /* parser_set_show_instrs */
