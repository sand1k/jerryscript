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

#include "bytecode-data.h"
#include "ecma-helpers.h"
#include "hash-table.h"
#include "jrt-libc-includes.h"
#include "jsp-mm.h"
#include "opcodes.h"
#include "opcodes-dumper.h"
#include "parser.h"
#include "re-parser.h"
#include "scopes-tree.h"
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
  JSP_STATE_EXPR__BEGIN,

  JSP_STATE_EXPR_EMPTY,               /**< no expression yet (at start) */
  JSP_STATE_EXPR_FUNCTION,            /**< FunctionExpression (11.2.5) */
  JSP_STATE_EXPR_MEMBER,              /**< MemberExpression (11.2) */
  JSP_STATE_EXPR_CALL,                /**< CallExpression (11.2) */
  JSP_STATE_EXPR_LEFTHANDSIDE,        /**< LeftHandSideExpression (11.2) */

  JSP_STATE_EXPR__SIMPLE_BEGIN,

  JSP_STATE_EXPR_UNARY,               /**< UnaryExpression (11.4) */
  JSP_STATE_EXPR_MULTIPLICATIVE,      /**< MultiplicativeExpression (11.5) */
  JSP_STATE_EXPR_ADDITIVE,            /**< AdditiveExpression (11.6) */
  JSP_STATE_EXPR_SHIFT,               /**< ShiftExpression (11.7) */
  JSP_STATE_EXPR_RELATIONAL,          /**< RelationalExpression (11.8) */
  JSP_STATE_EXPR_EQUALITY,            /**< EqualityExpression (11.9) */
  JSP_STATE_EXPR_BITWISE_AND,         /**< BitwiseAndExpression (11.10) */
  JSP_STATE_EXPR_BITWISE_XOR,         /**< BitwiseXorExpression (11.10) */
  JSP_STATE_EXPR_BITWISE_OR,          /**< BitwiseOrExpression (11.10) */

  JSP_STATE_EXPR__SIMPLE_END,

  JSP_STATE_EXPR_LOGICAL_AND,         /**< LogicalAndExpression (11.11) */
  JSP_STATE_EXPR_LOGICAL_OR,          /**< LogicalOrExpression (11.11) */
  JSP_STATE_EXPR_CONDITION,           /**< ConditionalExpression (11.12) */
  JSP_STATE_EXPR_ASSIGNMENT,          /**< AssignmentExpression (11.13) */
  JSP_STATE_EXPR_EXPRESSION,          /**< Expression (11.14) */

  JSP_STATE_EXPR_ARRAY_LITERAL,       /**< ArrayLiteral (11.1.4) */
  JSP_STATE_EXPR_OBJECT_LITERAL,      /**< ObjectLiteral (11.1.5) */

  JSP_STATE_EXPR_DATA_PROP_DECL,      /**< a data property (ObjectLiteral, 11.1.5) */
  JSP_STATE_EXPR_ACCESSOR_PROP_DECL,  /**< an accessor's property getter / setter (ObjectLiteral, 11.1.5) */

  JSP_STATE_EXPR__END,

  JSP_STATE_STAT_EMPTY,              /**< no statement yet (at start) */
  JSP_STATE_STAT_IF_BRANCH_START,    /**< IfStatement branch start */
  JSP_STATE_STAT_IF_BRANCH_END,      /**< IfStatement branch start */
  JSP_STATE_STAT_STATEMENT,          /**< Statement */
  JSP_STATE_STAT_STATEMENT_LIST,     /**< Statement list */
  JSP_STATE_STAT_VAR_DECL,           /**< VariableStatement */
  JSP_STATE_STAT_VAR_DECL_FINISH,
  JSP_STATE_STAT_DO_WHILE,           /**< IterationStatement */
  JSP_STATE_STAT_WHILE,
  JSP_STATE_STAT_FOR_INIT_END,
  JSP_STATE_STAT_FOR_INCREMENT,
  JSP_STATE_STAT_FOR_COND,
  JSP_STATE_STAT_FOR_FINISH,
  JSP_STATE_STAT_FOR_IN,
  JSP_STATE_STAT_FOR_IN_EXPR,
  JSP_STATE_STAT_FOR_IN_FINISH,
  JSP_STATE_STAT_ITER_FINISH,
  JSP_STATE_STAT_SWITCH,
  JSP_STATE_STAT_SWITCH_BRANCH_EXPR,
  JSP_STATE_STAT_SWITCH_BRANCH,
  JSP_STATE_STAT_SWITCH_FINISH,
  JSP_STATE_STAT_TRY,
  JSP_STATE_STAT_CATCH_FINISH,
  JSP_STATE_STAT_FINALLY_FINISH,
  JSP_STATE_STAT_TRY_FINISH,
  JSP_STATE_STAT_WITH,
  JSP_STATE_STAT_EXPRESSION,
  JSP_STATE_STAT_RETURN,
  JSP_STATE_STAT_THROW,

  JSP_STATE_FUNC_DECL_FINISH,
  JSP_STATE_SOURCE_ELEMENT_LIST,

  JSP_STATE_SOURCE_ELEMENTS_INIT,
  JSP_STATE_SOURCE_ELEMENTS,

  JSP_STATE_STAT_BLOCK,

  JSP_STATE_STAT_NAMED_LABEL
} jsp_state_expr_t;


typedef enum
{
  PREPARSE,
  DUMP
} jsp_parse_mode_t;

static void jsp_parse_source_element_list (jsp_parse_mode_t);

static bool
is_strict_mode (void)
{
  return scopes_tree_strict_mode (dumper_get_scope ());
}

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
  tok = lexer_next_token (false, is_strict_mode ());
}

/**
 * In case a regexp token is scanned as a division operator, rescan it
 */
static void
rescan_regexp_token (void)
{
  lexer_seek (tok.loc);
  tok = lexer_next_token (true, is_strict_mode ());
} /* rescan_regexp_token */

static void
seek_token (locus loc)
{
  lexer_seek (loc);

  skip_token ();
}

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
current_token_must_be_check_and_skip_it (jsp_token_type_t tt)
{
  if (!token_is (tt))
  {
    EMIT_ERROR_VARG (JSP_EARLY_ERROR_SYNTAX, "Expected '%s' token", lexer_token_type_to_string (tt));
  }

  skip_token ();
}

static void
current_token_must_be (jsp_token_type_t tt)
{
  if (!token_is (tt))
  {
    EMIT_ERROR_VARG (JSP_EARLY_ERROR_SYNTAX, "Expected '%s' token", lexer_token_type_to_string (tt));
  }
}

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
          seek_token (end_loc);

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
      scopes_tree_set_strict_mode (dumper_get_scope (), true);
      break;
    }

    skip_token ();

    if (token_is (TOK_SEMICOLON))
    {
      skip_token ();
    }
  }

  seek_token (start_loc);
} /* jsp_parse_directive_prologue */

static jsp_operand_t
jsp_start_parse_function_scope (jsp_operand_t func_name,
                                bool is_function_expression,
                                size_t *out_formal_parameters_num_p)
{
  scopes_tree parent_scope = dumper_get_scope ();
  scopes_tree_set_contains_functions (parent_scope);

  scopes_tree func_scope = scopes_tree_init (parent_scope, SCOPE_TYPE_FUNCTION);

  dumper_set_scope (func_scope);
  scopes_tree_set_strict_mode (func_scope, scopes_tree_strict_mode (parent_scope));

  /* parse formal parameters list */
  size_t formal_parameters_num = 0;

  current_token_must_be_check_and_skip_it (TOK_OPEN_PAREN);

  JERRY_ASSERT (func_name.is_empty_operand () || func_name.is_literal_operand ());

  varg_list_type vlt = is_function_expression ? VARG_FUNC_EXPR : VARG_FUNC_DECL;

  vm_instr_counter_t varg_header_pos = dump_varg_header_for_rewrite (vlt, func_name);

  locus formal_parameters_list_loc = tok.loc;

  while (!token_is (TOK_CLOSE_PAREN))
  {
    current_token_must_be (TOK_NAME);
    jsp_operand_t formal_parameter_name = literal_operand (token_data_as_lit_cp ());
    skip_token ();

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

  skip_token ();

  const jsp_operand_t func = is_function_expression ? tmp_operand () : empty_operand ();

  rewrite_varg_header_set_args_count (func, formal_parameters_num, varg_header_pos);

  dump_function_end_for_rewrite ();

  current_token_must_be_check_and_skip_it (TOK_OPEN_BRACE);

  jsp_parse_directive_prologue ();

  jsp_early_error_check_for_eval_and_arguments_in_strict_mode (func_name, is_strict_mode (), tok.loc);

  if (is_strict_mode ())
  {
    locus body_loc = tok.loc;

    seek_token (formal_parameters_list_loc);

    /* Check duplication of formal parameters names */
    while (!token_is (TOK_CLOSE_PAREN))
    {
      current_token_must_be (TOK_NAME);

      literal_t current_parameter_name_lit = lit_get_literal_by_cp (token_data_as_lit_cp ());
      locus current_parameter_loc = tok.loc;

      skip_token ();

      if (token_is (TOK_COMMA))
      {
        skip_token ();
      }

      jsp_early_error_emit_error_on_eval_and_arguments (current_parameter_name_lit,
                                                        current_parameter_loc);

      while (!token_is (TOK_CLOSE_PAREN))
      {
        current_token_must_be (TOK_NAME);

        if (lit_utf8_iterator_pos_cmp (tok.loc, current_parameter_loc) != 0)
        {
          literal_t iter_parameter_name_lit = lit_get_literal_by_cp (token_data_as_lit_cp ());

          if (lit_literal_equal_type (current_parameter_name_lit, iter_parameter_name_lit))
          {
            PARSE_ERROR_VARG (JSP_EARLY_ERROR_SYNTAX,
                              "Duplication of literal '%s' in FormalParameterList is not allowed in strict mode",
                              tok.loc, lit_literal_to_str_internal_buf (iter_parameter_name_lit));
          }
        }

        skip_token ();

        if (token_is (TOK_COMMA))
        {
          skip_token ();
        }
        else
        {
          current_token_must_be (TOK_CLOSE_PAREN);
        }
      }

      seek_token (current_parameter_loc);

      JERRY_ASSERT (lit_utf8_iterator_pos_cmp (tok.loc, current_parameter_loc) == 0);
      skip_token ();

      if (token_is (TOK_COMMA))
      {
        skip_token ();
      }
      else
      {
        current_token_must_be (TOK_CLOSE_PAREN);
      }
    }

    seek_token (body_loc);
  }

  if (out_formal_parameters_num_p != NULL)
  {
    *out_formal_parameters_num_p = formal_parameters_num;
  }

  return func;
}

static vm_instr_counter_t
jsp_find_function_end (void)
{
  scopes_tree scope_tree = dumper_get_scope ();
  JERRY_ASSERT (scope_tree->type == SCOPE_TYPE_FUNCTION);

  vm_instr_counter_t instr_pos = 0u;

  const vm_instr_counter_t header_oc = instr_pos++;
  op_meta header_opm = scopes_tree_op_meta (scope_tree, header_oc);
  JERRY_ASSERT (header_opm.op.op_idx == VM_OP_FUNC_EXPR_N || header_opm.op.op_idx == VM_OP_FUNC_DECL_N);

  while (true)
  {
    op_meta meta_opm = scopes_tree_op_meta (scope_tree, instr_pos);
    JERRY_ASSERT (meta_opm.op.op_idx == VM_OP_META);

    opcode_meta_type meta_type = (opcode_meta_type) meta_opm.op.data.meta.type;

    if (meta_type == OPCODE_META_TYPE_FUNCTION_END)
    {
      break;
    }
    else
    {
      JERRY_ASSERT (meta_type == OPCODE_META_TYPE_VARG);

      instr_pos++;
    }
  }

  return instr_pos;
}

static void
jsp_finish_parse_function_scope (bool is_function_expression)
{
  scopes_tree func_scope = dumper_get_scope ();
  JERRY_ASSERT (func_scope != NULL && func_scope->type == SCOPE_TYPE_FUNCTION);

  scopes_tree parent_scope = (scopes_tree) func_scope->t.parent;

  current_token_must_be_check_and_skip_it (TOK_CLOSE_BRACE);

  dump_ret ();

  vm_instr_counter_t function_end_pos = jsp_find_function_end ();

  rewrite_function_end (function_end_pos);

  dumper_set_scope (parent_scope);

  if (is_function_expression)
  {
    scopes_tree_merge_subscope (dumper_get_scope (), func_scope);
    scopes_tree_free (func_scope);
  }
}

typedef struct
{
  jsp_state_expr_t state; /**< current state */
  jsp_state_expr_t req_state; /**< required state */

  uint8_t is_completed              : 1; /**< the expression parse completed,
                                          *   no more tokens can be added to the expression */
  uint8_t is_list_in_process        : 1; /**< parsing a list, associated with the expression
                                          *   (details depend on current expression type) */
  uint8_t is_no_in_mode             : 1; /**< expression is being parsed in NoIn mode (see also: ECMA-262 v5, 11.8) */
  uint8_t is_fixed_ret_operand      : 1; /**< the expression's evaluation should produce value that should be
                                          *   put to register, specified by operand, specified in state */
  uint8_t is_value_based_reference : 1; /**< flag, indicating whether current state represents evaluated expression
                                         *   that evaluated to a value-based reference */
  uint8_t is_get_value_dumped_for_main_operand : 1;
  uint8_t is_get_value_dumped_for_prop_operand : 1;
  uint8_t is_need_retval            : 1; /**< flag, indicating whether result of the expression's
                                          *   evaluation, if it is value, is used */
  uint8_t is_complex_production     : 1; /**< the expression is being parsed in complex production mode */
  uint8_t var_decl                  : 1; /**< this flag tells that we are parsing VariableStatement, not
                                              VariableDeclarationList or VariableDeclaration inside
                                              IterationStatement */
  uint8_t is_var_decl_no_in         : 1; /**< this flag tells that we are parsing VariableDeclrationNoIn inside
                                              ForIn iteration statement */
  uint8_t was_default               : 1; /**< was default branch seen */
  uint8_t is_default_branch         : 1; /**< marks default branch of switch statement */
  uint8_t is_simply_jumpable_border : 1; /**< flag, indicating whether simple jump could be performed
                                          *   from current statement outside of the statement */
  uint8_t is_dump_eval_ret_store    : 1; /**< expression's result should be stored to eval's return register */
  uint8_t is_stmt_list_control_flow_exit_stmt_occured : 1; /**< flag, indicating whether one of the following statements
                                                            *   occured immediately in the statement list, corresponding
                                                            *   to the statement:
                                                            *     - return
                                                            *     - break
                                                            *     - continue
                                                            *     - throw */

  union u
  {
    u (void) { }

    struct expression
    {
      union u
      {
        struct
        {
          uint32_t list_length;
          vm_instr_counter_t header_pos; /**< position of a varg header instruction */
          vm_idx_t reg_alloc_saved_state;
        } varg_sequence;
        static_assert (sizeof (varg_sequence) == 8, "Please, update size if changed");

        struct
        {
          jsp_operand_t prop_name;
          bool is_setter;
        } accessor_prop_decl;
        static_assert (sizeof (accessor_prop_decl) == 6, "Please, update size if changed");

        struct
        {
          vm_instr_counter_t rewrite_chain; /**< chain of jmp instructions to rewrite */
        } logical_and;
        static_assert (sizeof (logical_and) == 2, "Please, update size if changed");

        struct
        {
          vm_instr_counter_t rewrite_chain; /**< chain of jmp instructions to rewrite */
        } logical_or;
        static_assert (sizeof (logical_or) == 2, "Please, update size if changed");

        struct
        {
          vm_instr_counter_t conditional_check_pos;
          vm_instr_counter_t jump_to_end_pos;
        } conditional;
        static_assert (sizeof (conditional) == 4, "Please, update size if changed");
      } u;
      static_assert (sizeof (u) == 8, "Please, update size if changed");

      jsp_operand_t operand; /**< operand, associated with expression */
      jsp_operand_t prop_name_operand; /**< operand, describing second part of a value-based reference,
                                        *   or empty operand (for Identifier references, values, or constants) */
      jsp_token_type_t token_type; /**< token, related to current and, if binary, to previous expression */
    } expression;
    static_assert (sizeof (expression) == 20, "Please, update size if changed");

    struct statement
    {
      union u
      {
        struct iterational
        {
          union u
          {
            struct loop_for_in
            {
              union u
              {
                locus iterator_expr_loc;
                locus body_loc;
              } u;

              lit_cpointer_t var_name_lit_cp;
              vm_instr_counter_t header_pos;
            } loop_for_in;
            static_assert (sizeof (loop_for_in) == 8, "Please, update size if changed");

            struct loop_while
            {
              union u
              {
                locus cond_expr_start_loc;
                locus end_loc;
              } u;

              vm_instr_counter_t next_iter_tgt_pos;
              vm_instr_counter_t jump_to_end_pos;
            } loop_while;
            static_assert (sizeof (loop_while) == 8, "Please, update size if changed");

            struct loop_do_while
            {
              vm_instr_counter_t next_iter_tgt_pos;
            } loop_do_while;
            static_assert (sizeof (loop_do_while) == 2, "Please, update size if changed");

            struct loop_for
            {
              union u1
              {
                locus body_loc;
                locus condition_expr_loc;
              } u1;

              union u2
              {
                locus increment_expr_loc;
                locus end_loc;
              } u2;

              vm_instr_counter_t next_iter_tgt_pos;
              vm_instr_counter_t jump_to_end_pos;
            } loop_for;
            static_assert (sizeof (loop_for) == 12, "Please, update size if changed");
          } u;
          static_assert (sizeof (u) == 12, "Please, update size if changed");

          vm_instr_counter_t continues_rewrite_chain;
          vm_instr_counter_t continue_tgt_oc;
        } iterational;
        static_assert (sizeof (iterational) == 16, "Please, update size if changed");

        struct if_statement
        {
          vm_instr_counter_t conditional_check_pos;
          vm_instr_counter_t jump_to_end_pos;
        } if_statement;
        static_assert (sizeof (if_statement) == 4, "Please, update size if changed");

        struct switch_statement
        {
          jsp_operand_t expr;

          vm_instr_counter_t default_label_oc; /**< MAX_OPCODES - if DefaultClause didn't occur,
                                                *   start of StatementList for the DefaultClause, otherwise */
          vm_instr_counter_t last_cond_check_jmp_oc; /**< position of last clause's check,
                                                      *   of MAX_OPCODES (at start, or after DefaultClause) */
          vm_instr_counter_t skip_check_jmp_oc; /**< position of check for whether next condition check
                                                    *   should be performed or skipped */
          vm_idx_t saved_reg_next;
          vm_idx_t saved_reg_max_for_temps;
        } switch_statement;
        static_assert (sizeof (switch_statement) == 12, "Please, update size if changed");

        struct with_statement
        {
          vm_instr_counter_t header_pos;
        } with_statement;
        static_assert (sizeof (with_statement) == 2, "Please, update size if changed");

        struct try_statement
        {
          vm_instr_counter_t try_pos;
          vm_instr_counter_t catch_pos;
          vm_instr_counter_t finally_pos;
        } try_statement;
        static_assert (sizeof (try_statement) == 6, "Please, update size if changed");
      } u;
      static_assert (sizeof (u) == 16, "Please, update size if changed");

      vm_instr_counter_t breaks_rewrite_chain;
    } statement;
    static_assert (sizeof (statement) == 20, "Please, update size if changed");

    struct named_label
    {
      lit_cpointer_t name_cp;
    } named_label;
    static_assert (sizeof (named_label) == 2, "Please, update size if changed");

    struct source_elements
    {
      vm_instr_counter_t scope_code_flags_oc;
      vm_instr_counter_t reg_var_decl_oc;

      vm_idx_t saved_reg_next;
      vm_idx_t saved_reg_max_for_temps;
    } source_elements;
    static_assert (sizeof (source_elements) == 6, "Please, update size if changed");
  } u;
  static_assert (sizeof (u) == 20, "Please, update size if changed");
} jsp_state_t;

static_assert (sizeof (jsp_state_t) == 24, "Please, update if size is changed");

/* FIXME: change to dynamic */
#define JSP_STATE_STACK_MAX 256
jsp_state_t* jsp_state_stack_p;
uint32_t jsp_state_stack_pos;

static void
jsp_stack_init (void)
{
  jsp_state_stack_p = (jsp_state_t *) jsp_mm_alloc (sizeof (jsp_state_t) * JSP_STATE_STACK_MAX);

  jsp_state_stack_pos = 0;
} /* jsp_stack_init */

static void
jsp_stack_finalize (void)
{
  jsp_mm_free (jsp_state_stack_p);
} /* jsp_stack_finalize */

static void
jsp_state_push (jsp_state_t state)
{
  if (jsp_state_stack_pos == JSP_STATE_STACK_MAX)
  {
    JERRY_UNREACHABLE ();
  }
  else
  {
    jsp_state_stack_p[jsp_state_stack_pos++] = state;
  }
} /* jsp_state_push */

static jsp_state_t *
jsp_get_prev_state (jsp_state_t *state_p)
{
  uint32_t pos = (uint32_t) (state_p - jsp_state_stack_p);

  JERRY_ASSERT (pos > 0u);

  return &jsp_state_stack_p[pos - 1u];
} /* jsp_get_prev_state */

static jsp_state_t *
jsp_get_next_state (jsp_state_t *state_p)
{
  uint32_t pos = (uint32_t) (state_p - jsp_state_stack_p);

  JERRY_ASSERT (pos + 1 < jsp_state_stack_pos);

  return &jsp_state_stack_p[pos + 1u];
} /* jsp_get_next_state */


static jsp_state_t *
jsp_state_top (void)
{
  JERRY_ASSERT (jsp_state_stack_pos > 0);

  return &jsp_state_stack_p[jsp_state_stack_pos - 1u];
} /* jsp_state_top */

static bool
jsp_is_stack_contains_exactly_one_element (void)
{
  return (jsp_state_stack_pos == 1);
} /* jsp_is_stack_contains_exactly_one_element */

static void
jsp_state_pop (void)
{
  JERRY_ASSERT (jsp_state_stack_pos > 0);

  --jsp_state_stack_pos;
} /* jsp_state_pop */

static void
jsp_push_new_expr_state (jsp_state_expr_t expr_type,
                         jsp_state_expr_t req_state,
                         bool in_allowed)
{
  jsp_state_t new_state;

  new_state.state = expr_type;
  new_state.req_state = req_state;
  new_state.u.expression.operand = empty_operand ();
  new_state.u.expression.prop_name_operand = empty_operand ();
  new_state.u.expression.token_type = TOK_EMPTY;

  new_state.is_completed = false;
  new_state.is_list_in_process = false;
  new_state.is_fixed_ret_operand = false;
  new_state.is_value_based_reference = false;
  new_state.is_complex_production = false;
  new_state.var_decl = false;
  new_state.is_var_decl_no_in = false;
  new_state.is_get_value_dumped_for_main_operand = false;
  new_state.is_get_value_dumped_for_prop_operand = false;
  new_state.is_need_retval = true;

  new_state.is_no_in_mode = !in_allowed;

  jsp_state_push (new_state);
} /* jsp_push_new_expr_state */

static bool
dump_get_value_for_state_if_ref (jsp_state_t *state_p,
                                 bool is_dump_for_value_based_refs_only,
                                 bool is_check_only)
{
  jsp_operand_t obj = state_p->u.expression.operand;
  jsp_operand_t prop_name = state_p->u.expression.prop_name_operand;
  bool is_value_based_reference = state_p->is_value_based_reference;

  jsp_operand_t val;

  bool is_dump = false;

  if (state_p->state == JSP_STATE_EXPR_LEFTHANDSIDE)
  {
    if (is_value_based_reference)
    {
      if (!state_p->is_get_value_dumped_for_main_operand)
      {
        JERRY_ASSERT (!state_p->is_get_value_dumped_for_prop_operand);
        /* FIXME:
             if (obj.is_identifier_operand ())
             {
             is_dump = true;

             if (!is_check_only)
             {
             jsp_operand_t general_reg = tmp_operand ();

             dump_variable_assignment (general_reg, obj);

             state_p->u.expression.operand = general_reg;
             state_p->is_get_value_dumped_for_main_operand = true;
             }
             }

             if (prop_name.is_identifier_operand ())
             {
             is_dump = true;

             if (!is_check_only)
             {
             jsp_operand_t general_reg = tmp_operand ();

             dump_variable_assignment (general_reg, prop_name);

             state_p->u.expression.prop_name_operand = general_reg;
             state_p->is_get_value_dumped_for_prop_operand = true;
             }
             }
         */
      }
    }
  }
  else
  {
    if (is_value_based_reference)
    {
        is_dump = true;

        JERRY_ASSERT (!prop_name.is_empty_operand ());

        if (!is_check_only)
        {
          jsp_operand_t reg = tmp_operand ();

          dump_prop_getter (reg, obj, prop_name);

          val = reg;

          state_p->is_get_value_dumped_for_main_operand = true;
          state_p->is_get_value_dumped_for_prop_operand = true;
        }
    }
    else if (!is_dump_for_value_based_refs_only
             && (obj.is_identifier_operand () || obj.is_this_operand ()))
    {
      if (!state_p->is_get_value_dumped_for_main_operand)
      {
        is_dump = true;

        if (!is_check_only)
        {
          jsp_operand_t general_reg = tmp_operand ();

          dump_variable_assignment (general_reg, obj);

          val = general_reg;

          state_p->is_get_value_dumped_for_main_operand = true;
        }
      }
    }

    if (!is_check_only && is_dump)
    {
      JERRY_ASSERT (state_p->is_get_value_dumped_for_main_operand);
      JERRY_ASSERT (!state_p->is_value_based_reference || state_p->is_get_value_dumped_for_prop_operand);

      state_p->u.expression.operand = val;
      state_p->u.expression.prop_name_operand = empty_operand ();
      state_p->is_value_based_reference = false;
    }
  }

  return is_dump;
}

static void
dump_get_value_for_prev_states (jsp_state_t *state_p)
{
  jsp_state_t *dump_state_border_for_p = jsp_get_prev_state (state_p);
  jsp_state_t *first_state_to_dump_for_p = state_p;

  while (dump_state_border_for_p != NULL)
  {
    if (dump_state_border_for_p->state > JSP_STATE_EXPR__BEGIN
        && dump_state_border_for_p->req_state < JSP_STATE_EXPR__END
        && (!dump_state_border_for_p->is_get_value_dumped_for_main_operand
            || !dump_state_border_for_p->is_get_value_dumped_for_prop_operand))
    {
      first_state_to_dump_for_p = dump_state_border_for_p;
      dump_state_border_for_p = jsp_get_prev_state (dump_state_border_for_p);
    }
    else
    {
      break;
    }
  }

  JERRY_ASSERT (first_state_to_dump_for_p != NULL);

  jsp_state_t *state_iter_p = first_state_to_dump_for_p;

  while (state_iter_p != state_p)
  {
    dump_get_value_for_state_if_ref (state_iter_p, false, false);

    state_iter_p = jsp_get_next_state (state_iter_p);
  }
}

static void
dump_get_value_if_ref (jsp_state_t *state_p,
                       bool is_dump_for_value_based_refs_only)
{
  if (dump_get_value_for_state_if_ref (state_p, is_dump_for_value_based_refs_only, true))
  {
    dump_get_value_for_prev_states (state_p);

    dump_get_value_for_state_if_ref (state_p, is_dump_for_value_based_refs_only, false);
  }
}

static vm_instr_counter_t
jsp_start_call_dump (jsp_state_t *state_p)
{
  jsp_operand_t obj = state_p->u.expression.operand;
  jsp_operand_t prop_name = state_p->u.expression.prop_name_operand;
  bool is_value_based_reference = state_p->is_value_based_reference;

  opcode_call_flags_t call_flags = OPCODE_CALL_FLAGS__EMPTY;

  jsp_operand_t val;

  if (is_value_based_reference)
  {
    if (obj.is_identifier_operand ()
        && !state_p->is_get_value_dumped_for_main_operand)
    {
      jsp_operand_t reg = tmp_operand ();

      dump_variable_assignment (reg, obj);

      obj = reg;

      state_p->is_get_value_dumped_for_main_operand = true;
    }

    val = tmp_operand ();
    dump_prop_getter (val, obj, prop_name);

    state_p->is_get_value_dumped_for_prop_operand = true;

    call_flags = (opcode_call_flags_t) (call_flags | OPCODE_CALL_FLAGS_HAVE_THIS_ARG);

    /*
     * Presence of explicit 'this' argument implies that this is not Direct call to Eval
     *
     * See also:
     *          ECMA-262 v5, 15.2.2.1
     */
  }
  else
  {
    if (dumper_is_eval_literal (obj))
    {
      call_flags = (opcode_call_flags_t) (call_flags | OPCODE_CALL_FLAGS_DIRECT_CALL_TO_EVAL_FORM);
    }

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
    val = obj;

    state_p->is_get_value_dumped_for_main_operand = true;
  }

  vm_instr_counter_t varg_header_pos = dump_varg_header_for_rewrite (VARG_CALL_EXPR, val);

  if (call_flags != OPCODE_CALL_FLAGS__EMPTY)
  {
    if (call_flags & OPCODE_CALL_FLAGS_HAVE_THIS_ARG)
    {
      dump_call_additional_info (call_flags, obj);
    }
    else
    {
      dump_call_additional_info (call_flags, empty_operand ());
    }
  }

  state_p->u.expression.operand = empty_operand ();
  state_p->u.expression.prop_name_operand = empty_operand ();
  state_p->is_value_based_reference = false;

  return varg_header_pos;
} /* jsp_start_call_dump */

static jsp_operand_t
jsp_finish_call_dump (uint32_t args_num,
                      vm_instr_counter_t header_pos)
{
  jsp_operand_t ret = tmp_operand ();

  rewrite_varg_header_set_args_count (ret, args_num, header_pos);

  return ret;
} /* jsp_finish_call_dump */

static vm_instr_counter_t __attr_unused___
jsp_start_construct_dump (jsp_state_t *state_p)
{
  dump_get_value_if_ref (state_p, true);

  state_p->is_get_value_dumped_for_main_operand = true;

  return dump_varg_header_for_rewrite (VARG_CONSTRUCT_EXPR, state_p->u.expression.operand);
} /* jsp_start_construct_dump */

static jsp_operand_t __attr_unused___
jsp_finish_construct_dump (uint32_t args_num,
                           vm_instr_counter_t header_pos)
{
  jsp_operand_t ret = tmp_operand ();

  rewrite_varg_header_set_args_count (ret, args_num, header_pos);

  return ret;
} /* jsp_finish_construct_dump */

static void
jsp_add_nested_jump_to_rewrite_chain (vm_instr_counter_t *in_out_rewrite_chain_p)
{
  *in_out_rewrite_chain_p = dump_simple_or_nested_jump_for_rewrite (true, false, false,
                                                                    empty_operand (),
                                                                    *in_out_rewrite_chain_p);
}

static void
jsp_add_simple_jump_to_rewrite_chain (vm_instr_counter_t *in_out_rewrite_chain_p)
{
  *in_out_rewrite_chain_p = dump_simple_or_nested_jump_for_rewrite (false, false, false,
                                                                    empty_operand (),
                                                                    *in_out_rewrite_chain_p);
}

static void
jsp_add_conditional_jump_to_rewrite_chain (vm_instr_counter_t *in_out_rewrite_chain_p,
                                           bool is_inverted_condition,
                                           jsp_operand_t condition)
{
  *in_out_rewrite_chain_p = dump_simple_or_nested_jump_for_rewrite (false, true, is_inverted_condition,
                                                                    condition,
                                                                    *in_out_rewrite_chain_p);
}

static uint32_t
jsp_rewrite_jumps_chain (vm_instr_counter_t *rewrite_chain_p,
                         vm_instr_counter_t target_oc)
{
  uint32_t count = 0;

  while (*rewrite_chain_p != MAX_OPCODES)
  {
    count++;

    *rewrite_chain_p = rewrite_simple_or_nested_jump_and_get_next (*rewrite_chain_p,
                                                                   target_oc);
  }

  return count;
} /* jsp_rewrite_jumps_chain */

static bool
jsp_is_assignment_expression_end (jsp_state_t *current_state_p)
{
  jsp_token_type_t tt = lexer_get_token_type (tok);

  JERRY_ASSERT (current_state_p->state == JSP_STATE_EXPR_UNARY
                || current_state_p->state == JSP_STATE_EXPR_MULTIPLICATIVE
                || current_state_p->state == JSP_STATE_EXPR_ADDITIVE
                || current_state_p->state == JSP_STATE_EXPR_SHIFT
                || current_state_p->state == JSP_STATE_EXPR_RELATIONAL
                || current_state_p->state == JSP_STATE_EXPR_EQUALITY
                || current_state_p->state == JSP_STATE_EXPR_BITWISE_AND
                || current_state_p->state == JSP_STATE_EXPR_BITWISE_XOR
                || current_state_p->state == JSP_STATE_EXPR_BITWISE_OR);

  if ((tt >= TOKEN_TYPE__MULTIPLICATIVE_BEGIN
       && tt <= TOKEN_TYPE__MULTIPLICATIVE_END)
      || (tt >= TOKEN_TYPE__ADDITIVE_BEGIN
          && tt <= TOKEN_TYPE__ADDITIVE_END)
      || (tt >= TOKEN_TYPE__SHIFT_BEGIN
          && tt <= TOKEN_TYPE__SHIFT_END)
      || (tt >= TOKEN_TYPE__RELATIONAL_BEGIN
          && tt <= TOKEN_TYPE__RELATIONAL_END)
      || (tt >= TOKEN_TYPE__EQUALITY_BEGIN
          && tt <= TOKEN_TYPE__EQUALITY_END)
      || (tt == TOK_AND)
      || (tt == TOK_XOR)
      || (tt == TOK_OR)
      || (tt == TOK_DOUBLE_AND)
      || (tt == TOK_DOUBLE_OR)
      || (tt == TOK_QUERY))
  {
    return false;
  }

  return true;
}

static bool
jsp_dump_unary_op (jsp_state_t *state_p,
                   jsp_state_t *substate_p)
{
  vm_op_t opcode;

  bool is_combined_with_assignment = false;

  jsp_state_t *prev_state_p = jsp_get_prev_state (state_p);
  JERRY_ASSERT (prev_state_p != NULL);

  bool is_try_combine_with_assignment = (prev_state_p->state == JSP_STATE_EXPR_LEFTHANDSIDE
                                         && prev_state_p->u.expression.token_type == TOK_EQ
                                         && !prev_state_p->is_value_based_reference
                                         && !prev_state_p->is_need_retval
                                         && jsp_is_assignment_expression_end (state_p));

  jsp_token_type_t tt = state_p->u.expression.token_type;
  state_p->u.expression.token_type = TOK_EMPTY;

  bool is_dump_simple_assignment = false;
  bool is_dump_undefined_or_boolean_true = true; /* the value is not valid until is_dump_simple_assignment is set */

  switch (tt)
  {
    case TOK_DOUBLE_PLUS:
    case TOK_DOUBLE_MINUS:
    {
      if (!substate_p->is_value_based_reference)
      {
        if (substate_p->u.expression.operand.is_identifier_operand ())
        {
          jsp_early_error_check_for_eval_and_arguments_in_strict_mode (substate_p->u.expression.operand,
                                                                       is_strict_mode (),
                                                                       tok.loc);
        }
        else
        {
          PARSE_ERROR (JSP_EARLY_ERROR_REFERENCE, "Invalid left-hand-side expression", tok.loc);
        }
      }

      opcode = (tt == TOK_DOUBLE_PLUS ? VM_OP_PRE_INCR : VM_OP_PRE_DECR);
      break;
    }
    case TOK_PLUS:
    {
      dump_get_value_if_ref (substate_p, true);

      opcode = VM_OP_UNARY_PLUS;
      break;
    }
    case TOK_MINUS:
    {
      dump_get_value_if_ref (substate_p, true);

      opcode = VM_OP_UNARY_MINUS;
      break;
    }
    case TOK_COMPL:
    {
      dump_get_value_if_ref (substate_p, true);

      opcode = VM_OP_B_NOT;
      break;
    }
    case TOK_NOT:
    {
      dump_get_value_if_ref (substate_p, true);

      opcode = VM_OP_LOGICAL_NOT;
      break;
    }
    case TOK_KW_DELETE:
    {
      if (substate_p->is_value_based_reference)
      {
        opcode = VM_OP_DELETE_PROP;
      }
      else if (substate_p->u.expression.operand.is_identifier_operand ())
      {
        jsp_early_error_check_delete (is_strict_mode (), tok.loc);

        opcode = VM_OP_DELETE_VAR;
      }
      else
      {
        opcode = VM_OP__COUNT /* invalid opcode as it will not be used */;

        is_dump_simple_assignment = true;
        is_dump_undefined_or_boolean_true = false; /* dump boolean true value */
      }
      break;
    }
    case TOK_KW_VOID:
    {
      dump_get_value_if_ref (substate_p, false);

      opcode = VM_OP__COUNT /* invalid opcode as it will not be used */;

      is_dump_simple_assignment = true;
      is_dump_undefined_or_boolean_true = true; /* dump undefined value */
      break;
    }
    default:
    {
      dump_get_value_if_ref (substate_p, true);

      JERRY_ASSERT (tt == TOK_KW_TYPEOF);

      opcode = VM_OP_TYPEOF;
      break;
    }
  }

  jsp_operand_t dst;

  if (dump_get_value_for_state_if_ref (substate_p, false, true))
  {
    dump_get_value_for_prev_states (substate_p);
  }

  if (is_try_combine_with_assignment
      && (is_dump_simple_assignment
          || !substate_p->is_value_based_reference
          || opcode == VM_OP_DELETE_PROP))
  {
    dst = prev_state_p->u.expression.operand;

    is_combined_with_assignment = true;
  }
  else
  {
    dst = tmp_operand ();
  }

  if (is_dump_simple_assignment)
  {
    if (is_dump_undefined_or_boolean_true)
    {
      dump_undefined_assignment (dst);
    }
    else
    {
      dump_boolean_assignment (dst, true);
    }
  }
  else
  {
    if (substate_p->is_value_based_reference)
    {
      if (opcode == VM_OP_DELETE_PROP)
      {
        dump_binary_op (VM_OP_DELETE_PROP,
                        dst,
                        substate_p->u.expression.operand,
                        substate_p->u.expression.prop_name_operand);
      }
      else
      {
        JERRY_ASSERT (opcode == VM_OP_PRE_INCR || opcode == VM_OP_PRE_DECR);

        jsp_operand_t reg = tmp_operand ();

        dump_prop_getter (reg, substate_p->u.expression.operand, substate_p->u.expression.prop_name_operand);

        dump_unary_op (opcode, reg, reg);

        dump_prop_setter (substate_p->u.expression.operand, substate_p->u.expression.prop_name_operand, reg);

        dst = reg;
      }
    }
    else
    {
      JERRY_ASSERT (!substate_p->is_value_based_reference);

      dump_unary_op (opcode, dst, substate_p->u.expression.operand);
    }
  }

  JERRY_ASSERT (!state_p->is_value_based_reference);
  state_p->u.expression.operand = dst;

  return is_combined_with_assignment;
}

static bool
jsp_dump_binary_op (jsp_state_t *state_p,
                    jsp_state_t *substate_p)
{
  vm_op_t opcode;

  bool is_combined_with_assignment = false;

  jsp_state_t *prev_state_p = jsp_get_prev_state (state_p);
  JERRY_ASSERT (prev_state_p != NULL);

  bool is_try_combine_with_assignment = (prev_state_p->state == JSP_STATE_EXPR_LEFTHANDSIDE
                                         && prev_state_p->u.expression.token_type == TOK_EQ
                                         && !prev_state_p->is_value_based_reference
                                         && !prev_state_p->is_need_retval
                                         && jsp_is_assignment_expression_end (state_p));

  jsp_token_type_t tt = state_p->u.expression.token_type;
  state_p->u.expression.token_type = TOK_EMPTY;

  switch (tt)
  {
    case TOK_MULT:
    {
      opcode = VM_OP_MULTIPLICATION;
      break;
    }
    case TOK_DIV:
    {
      opcode = VM_OP_DIVISION;
      break;
    }
    case TOK_MOD:
    {
      opcode = VM_OP_REMAINDER;
      break;
    }
    case TOK_PLUS:
    {
      opcode = VM_OP_ADDITION;
      break;
    }
    case TOK_MINUS:
    {
      opcode = VM_OP_SUBSTRACTION;
      break;
    }
    case TOK_LSHIFT:
    {
      opcode = VM_OP_B_SHIFT_LEFT;
      break;
    }
    case TOK_RSHIFT:
    {
      opcode = VM_OP_B_SHIFT_RIGHT;
      break;
    }
    case TOK_RSHIFT_EX:
    {
      opcode = VM_OP_B_SHIFT_URIGHT;
      break;
    }
    case TOK_LESS:
    {
      opcode = VM_OP_LESS_THAN;
      break;
    }
    case TOK_GREATER:
    {
      opcode = VM_OP_GREATER_THAN;
      break;
    }
    case TOK_LESS_EQ:
    {
      opcode = VM_OP_LESS_OR_EQUAL_THAN;
      break;
    }
    case TOK_GREATER_EQ:
    {
      opcode = VM_OP_GREATER_OR_EQUAL_THAN;
      break;
    }
    case TOK_KW_INSTANCEOF:
    {
      opcode = VM_OP_INSTANCEOF;
      break;
    }
    case TOK_KW_IN:
    {
      opcode = VM_OP_IN;
      break;
    }
    case TOK_DOUBLE_EQ:
    {
      opcode = VM_OP_EQUAL_VALUE;
      break;
    }
    case TOK_NOT_EQ:
    {
      opcode = VM_OP_NOT_EQUAL_VALUE;
      break;
    }
    case TOK_TRIPLE_EQ:
    {
      opcode = VM_OP_EQUAL_VALUE_TYPE;
      break;
    }
    case TOK_NOT_DOUBLE_EQ:
    {
      opcode = VM_OP_NOT_EQUAL_VALUE_TYPE;
      break;
    }
    case TOK_AND:
    {
      opcode = VM_OP_B_AND;
      break;
    }
    case TOK_XOR:
    {
      opcode = VM_OP_B_XOR;
      break;
    }
    default:
    {
      JERRY_ASSERT (tt == TOK_OR);

      opcode = VM_OP_B_OR;
      break;
    }
  }

  jsp_operand_t dst, op1, op2;

  if (!state_p->is_value_based_reference
      && !substate_p->is_value_based_reference)
  {
    if (dump_get_value_for_state_if_ref (state_p, false, true)
        || dump_get_value_for_state_if_ref (substate_p, false, true))
    {
      dump_get_value_for_prev_states (state_p);
    }

    op1 = state_p->u.expression.operand;
    op2 = substate_p->u.expression.operand;

    if (is_try_combine_with_assignment)
    {
      dst = prev_state_p->u.expression.operand;

      is_combined_with_assignment = true;
    }
    else if (op1.is_register_operand ())
    {
      dst = op1;
    }
    else
    {
      dst = tmp_operand ();
    }
  }
  else
  {
    dump_get_value_if_ref (state_p, true);
    dump_get_value_if_ref (substate_p, true);

    if (is_try_combine_with_assignment)
    {
      dst = prev_state_p->u.expression.operand;

      is_combined_with_assignment = true;
    }
    else
    {
      dst = state_p->u.expression.operand;
    }

    op1 = state_p->u.expression.operand;
    op2 = substate_p->u.expression.operand;
  }

  JERRY_ASSERT (!state_p->is_value_based_reference);
  state_p->u.expression.operand = dst;

  dump_binary_op (opcode, dst, op1, op2);

  return is_combined_with_assignment;
}

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
jsp_try_move_vars_to_regs (jsp_state_t *state_p,
                           opcode_scope_code_flags_t scope_flags)
{
  JERRY_ASSERT (state_p->state == JSP_STATE_SOURCE_ELEMENTS);

  scopes_tree fe_scope_tree = dumper_get_scope ();

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

      vm_instr_counter_t function_end_pos = jsp_find_function_end ();

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

            state_p->u.source_elements.scope_code_flags_oc--;
            state_p->u.source_elements.reg_var_decl_oc--;
          }
        }
      }
    }
  }

  return scope_flags;
}
#endif /* CONFIG_PARSER_ENABLE_PARSE_TIME_BYTE_CODE_OPTIMIZER */

static void
parse_expression_inside_parens_begin (void)
{
  current_token_must_be_check_and_skip_it (TOK_OPEN_PAREN);
}

static void
parse_expression_inside_parens_end (void)
{
  current_token_must_be_check_and_skip_it (TOK_CLOSE_PAREN);
}

static void
jsp_start_statement_parse (jsp_state_expr_t stat)
{
  jsp_state_t new_state;

  new_state.state = stat;
  new_state.req_state = JSP_STATE_STAT_STATEMENT;

  new_state.u.statement.breaks_rewrite_chain = MAX_OPCODES;

  new_state.is_completed = false;
  new_state.is_list_in_process = false;
  new_state.is_no_in_mode = false;
  new_state.is_fixed_ret_operand = false;
  new_state.is_complex_production = false;
  new_state.var_decl = false;
  new_state.was_default = false;
  new_state.is_default_branch = false;
  new_state.is_simply_jumpable_border = false;
  new_state.is_stmt_list_control_flow_exit_stmt_occured = false;

  jsp_state_push (new_state);
} /* jsp_start_statement_parse */

static jsp_state_t *
jsp_find_unnamed_label (bool is_label_for_break,
                        bool *out_is_simply_jumpable_p)
{
  *out_is_simply_jumpable_p = true;

  uint32_t stack_pos = jsp_state_stack_pos;

  while (stack_pos != 0)
  {
    jsp_state_t *state_p = &jsp_state_stack_p [--stack_pos];

    if (state_p->state == JSP_STATE_SOURCE_ELEMENTS)
    {
      break;
    }

    if (state_p->is_simply_jumpable_border)
    {
      *out_is_simply_jumpable_p = false;
    }

    bool is_iterational_stmt = (state_p->state == JSP_STATE_STAT_WHILE
                                || state_p->state == JSP_STATE_STAT_DO_WHILE
                                || state_p->state == JSP_STATE_STAT_FOR_IN
                                || state_p->state == JSP_STATE_STAT_FOR_IN_EXPR
                                || state_p->state == JSP_STATE_STAT_FOR_IN_FINISH
                                || state_p->state == JSP_STATE_STAT_FOR_INCREMENT);
    bool is_switch_stmt = (state_p->state == JSP_STATE_STAT_SWITCH_BRANCH_EXPR);

    if ((is_switch_stmt && is_label_for_break) || is_iterational_stmt)
    {
      return state_p;
    }
  }

  return NULL;
}

static jsp_state_t *
jsp_find_named_label (lit_cpointer_t name_cp,
                      bool *out_is_simply_jumpable_p)
{
  *out_is_simply_jumpable_p = true;

  uint32_t stack_pos = jsp_state_stack_pos;

  while (stack_pos != 0)
  {
    jsp_state_t *state_p = &jsp_state_stack_p [--stack_pos];

    if (state_p->state == JSP_STATE_SOURCE_ELEMENTS)
    {
      break;
    }

    if (state_p->is_simply_jumpable_border)
    {
      *out_is_simply_jumpable_p = false;
    }

    if (state_p->state == JSP_STATE_STAT_NAMED_LABEL
        && state_p->u.named_label.name_cp.packed_value == name_cp.packed_value)
    {
      while (++stack_pos < jsp_state_stack_pos)
      {
        state_p = &jsp_state_stack_p [stack_pos];

        if (state_p->state != JSP_STATE_STAT_NAMED_LABEL)
        {
          break;
        }
      }

      JERRY_ASSERT (stack_pos < jsp_state_stack_pos);

      return state_p;
    }
  }

  return NULL;
}

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
  JERRY_ASSERT (substate_p == NULL); \
  state_p->state = JSP_STATE_STAT_STATEMENT; \
  JERRY_ASSERT (!state_p->is_completed); \
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

#define JSP_FINISH_SUBEXPR() \
  JERRY_ASSERT (substate_p == jsp_state_top ()); \
  substate_p = NULL; \
  jsp_state_pop (); \
  JERRY_ASSERT (state_p == jsp_state_top ());

#define JSP_ASSIGNMENT_EXPR_COMBINE() \
  jsp_state_pop (); \
  state_p = jsp_state_top (); \
  JERRY_ASSERT (state_p->state == JSP_STATE_EXPR_LEFTHANDSIDE); \
  JERRY_ASSERT (!state_p->is_need_retval); \
  state_p->state = JSP_STATE_EXPR_ASSIGNMENT; \
  state_p->u.expression.operand = empty_operand (); \
  state_p->u.expression.token_type = TOK_EMPTY; \
  state_p->is_completed = true;

/**
 * Parse source element list
 */
static void __attr_noinline___
jsp_parse_source_element_list (jsp_parse_mode_t parse_mode)
{
  dumper_set_generate_bytecode (parse_mode == DUMP);

  jsp_start_statement_parse (JSP_STATE_SOURCE_ELEMENTS_INIT);
  jsp_state_top ()->req_state = JSP_STATE_SOURCE_ELEMENTS;

  while (true)
  {
    bool is_source_elements_list_end = false;
    bool is_stmt_list_end = false, is_stmt_list_control_flow_exit_stmt_occured = false;
    bool is_subexpr_end = false;

    jsp_state_t *state_p = jsp_state_top (), *substate_p = NULL;

    if (state_p->state == state_p->req_state && state_p->is_completed)
    {
      if (jsp_is_stack_contains_exactly_one_element ())
      {
        JERRY_ASSERT (state_p->state == JSP_STATE_SOURCE_ELEMENTS);

        jsp_state_pop ();

        return;
      }
      else
      {
        is_subexpr_end = (state_p->state > JSP_STATE_EXPR__BEGIN && state_p->state < JSP_STATE_EXPR__END);

        if (is_subexpr_end)
        {
          substate_p = state_p;
          state_p = jsp_get_prev_state (state_p);
        }
        else
        {
          if (state_p->req_state == JSP_STATE_SOURCE_ELEMENTS)
          {
            is_source_elements_list_end = true;
          }
          else if (state_p->req_state == JSP_STATE_STAT_STATEMENT_LIST)
          {
            is_stmt_list_end = true;

            is_stmt_list_control_flow_exit_stmt_occured = state_p->is_stmt_list_control_flow_exit_stmt_occured;
          }

          JERRY_ASSERT (state_p->is_completed);
          jsp_state_pop ();

          state_p = jsp_state_top ();
        }
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
      JERRY_ASSERT (!(state_p->state == JSP_STATE_EXPR_EXPRESSION && state_p->req_state != JSP_STATE_EXPR_EXPRESSION));
    }

    const bool in_allowed = !state_p->is_no_in_mode;

    if (state_p->state == JSP_STATE_SOURCE_ELEMENTS_INIT)
    {
      scope_type_t scope_type = dumper_get_scope ()->type;

      dumper_save_reg_alloc_ctx (&state_p->u.source_elements.saved_reg_next,
                                 &state_p->u.source_elements.saved_reg_max_for_temps);

      state_p->u.source_elements.scope_code_flags_oc = dump_scope_code_flags_for_rewrite ();
      state_p->u.source_elements.reg_var_decl_oc = dump_reg_var_decl_for_rewrite ();

      if (scope_type == SCOPE_TYPE_EVAL)
      {
        dump_undefined_assignment (jsp_operand_t::make_reg_operand (VM_REG_SPECIAL_EVAL_RET));
      }

      state_p->state = JSP_STATE_SOURCE_ELEMENTS;
    }
    else if (state_p->state == JSP_STATE_SOURCE_ELEMENTS)
    {
      scope_type_t scope_type = dumper_get_scope ()->type;

      jsp_token_type_t end_token_type = (scope_type == SCOPE_TYPE_FUNCTION) ? TOK_CLOSE_BRACE : TOK_EOF;

      if (token_is (end_token_type))
      {
        opcode_scope_code_flags_t scope_flags = OPCODE_SCOPE_CODE_FLAGS__EMPTY;

        scopes_tree fe_scope_tree = dumper_get_scope ();
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
        scope_flags = jsp_try_move_vars_to_regs (state_p, scope_flags);
#endif /* CONFIG_PARSER_ENABLE_PARSE_TIME_BYTE_CODE_OPTIMIZER */

        rewrite_scope_code_flags (state_p->u.source_elements.scope_code_flags_oc, scope_flags);
        rewrite_reg_var_decl (state_p->u.source_elements.reg_var_decl_oc);

        state_p->is_completed = true;

        dumper_restore_reg_alloc_ctx (state_p->u.source_elements.saved_reg_next,
                                      state_p->u.source_elements.saved_reg_max_for_temps);
      }
      else
      {
        JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_SOURCE_ELEMENTS);
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_EMPTY)
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
        state_p->u.expression.token_type = tt;

        if (tt == TOK_KW_DELETE)
        {
          scopes_tree_set_contains_delete (dumper_get_scope ());
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
        dump_get_value_for_prev_states (state_p);

        /* ArrayLiteral */
        vm_instr_counter_t varg_header_pos = dump_varg_header_for_rewrite (VARG_ARRAY_DECL, empty_operand ());

        state_p->state = JSP_STATE_EXPR_ARRAY_LITERAL;
        state_p->is_list_in_process = true;
        state_p->u.expression.u.varg_sequence.list_length = 0;
        state_p->u.expression.u.varg_sequence.header_pos = varg_header_pos;
      }
      else if (token_is (TOK_OPEN_BRACE))
      {
        dump_get_value_for_prev_states (state_p);

        /* ObjectLiteral */
        vm_instr_counter_t varg_header_pos = dump_varg_header_for_rewrite (VARG_OBJ_DECL, empty_operand ());
        jsp_early_error_start_checking_of_prop_names ();

        state_p->state = JSP_STATE_EXPR_OBJECT_LITERAL;
        state_p->is_list_in_process = true;
        state_p->u.expression.u.varg_sequence.list_length = 0;
        state_p->u.expression.u.varg_sequence.header_pos = varg_header_pos;
      }
      else
      {
        /* MemberExpression (PrimaryExpression is immediately promoted to MemberExpression) */
        state_p->state = JSP_STATE_EXPR_MEMBER;

        switch (lexer_get_token_type (tok))
        {
          case TOK_OPEN_PAREN:
          {
            state_p->u.expression.token_type = TOK_OPEN_PAREN;

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);

            jsp_state_top ()->is_need_retval = state_p->is_need_retval;

            break;
          }
          case TOK_KW_THIS:
          {
            state_p->u.expression.operand = jsp_operand_t::make_this_operand ();
            break;
          }
          case TOK_KW_NEW:
          {
            state_p->state = JSP_STATE_EXPR_MEMBER;
            state_p->u.expression.token_type = TOK_KW_NEW;

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_MEMBER, true);
            break;
          }
          case TOK_NAME:
          {
            if (lit_literal_equal_type_cstr (lit_get_literal_by_cp (token_data_as_lit_cp ()), "arguments"))
            {
              scopes_tree_set_arguments_used (dumper_get_scope ());
            }
            if (lit_literal_equal_type_cstr (lit_get_literal_by_cp (token_data_as_lit_cp ()), "eval"))
            {
              scopes_tree_set_eval_used (dumper_get_scope ());
            }

            state_p->u.expression.operand = jsp_operand_t::make_identifier_operand (token_data_as_lit_cp ());

            break;
          }
          case TOK_REGEXP:
          {
            state_p->u.expression.operand = tmp_operand ();
            dump_regexp_assignment (state_p->u.expression.operand, token_data_as_lit_cp ());
            break;
          }
          case TOK_NULL:
          {
            state_p->u.expression.operand = tmp_operand ();
            dump_null_assignment (state_p->u.expression.operand);
            break;
          }
          case TOK_BOOL:
          {
            state_p->u.expression.operand = tmp_operand ();
            dump_boolean_assignment (state_p->u.expression.operand, (bool) token_data ());
            break;
          }
          case TOK_SMALL_INT:
          {
            state_p->u.expression.operand = tmp_operand ();
            dump_smallint_assignment (state_p->u.expression.operand, (vm_idx_t) token_data ());
            break;
          }
          case TOK_NUMBER:
          {
            state_p->u.expression.operand = tmp_operand ();
            dump_number_assignment (state_p->u.expression.operand, token_data_as_lit_cp ());
            break;
          }
          case TOK_STRING:
          {
            state_p->u.expression.operand = tmp_operand ();
            dump_string_assignment (state_p->u.expression.operand, token_data_as_lit_cp ());
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
    else if (state_p->state == JSP_STATE_EXPR_FUNCTION)
    {
      JERRY_ASSERT (!state_p->is_completed);

      if (is_source_elements_list_end)
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

        state_p->u.expression.operand = jsp_start_parse_function_scope (name, true, NULL);

        jsp_start_statement_parse (JSP_STATE_SOURCE_ELEMENTS_INIT);
        jsp_state_top ()->req_state = JSP_STATE_SOURCE_ELEMENTS;
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_DATA_PROP_DECL)
    {
      JERRY_ASSERT (!state_p->is_completed);

      if (is_subexpr_end)
      {
        JERRY_ASSERT (substate_p->state == JSP_STATE_EXPR_ASSIGNMENT);

        dump_get_value_if_ref (substate_p, true);

        jsp_operand_t prop_name = state_p->u.expression.operand;
        jsp_operand_t value = substate_p->u.expression.operand;

        JERRY_ASSERT (prop_name.is_literal_operand ());

        dump_prop_name_and_value (prop_name, value);
        jsp_early_error_add_prop_name (prop_name, PROP_DATA);

        state_p->is_completed = true;

        JSP_FINISH_SUBEXPR ();
      }
      else
      {
        JERRY_ASSERT (state_p->u.expression.operand.is_empty_operand ());
        state_p->u.expression.operand = parse_property_name ();
        skip_token ();

        JERRY_ASSERT (token_is (TOK_COLON));
        skip_token ();

        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_ACCESSOR_PROP_DECL)
    {
      JERRY_ASSERT (!state_p->is_completed);

      if (is_source_elements_list_end)
      {
        jsp_finish_parse_function_scope (true);

        jsp_operand_t prop_name = state_p->u.expression.u.accessor_prop_decl.prop_name;
        jsp_operand_t func = state_p->u.expression.operand;
        bool is_setter = state_p->u.expression.u.accessor_prop_decl.is_setter;

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

        skip_token ();

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

        JERRY_ASSERT (state_p->u.expression.operand.is_empty_operand ());
        state_p->u.expression.operand = func;

        state_p->u.expression.u.accessor_prop_decl.prop_name = prop_name;
        state_p->u.expression.u.accessor_prop_decl.is_setter = is_setter;

        jsp_start_statement_parse (JSP_STATE_SOURCE_ELEMENTS_INIT);
        jsp_state_top ()->req_state = JSP_STATE_SOURCE_ELEMENTS;
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_OBJECT_LITERAL)
    {
      JERRY_ASSERT (!state_p->is_completed);
      JERRY_ASSERT (state_p->is_list_in_process);

      if (is_subexpr_end)
      {
        JERRY_ASSERT (substate_p->state == JSP_STATE_EXPR_DATA_PROP_DECL
                      || substate_p->state == JSP_STATE_EXPR_ACCESSOR_PROP_DECL);

        state_p->u.expression.u.varg_sequence.list_length++;

        dumper_finish_varg_code_sequence (state_p->u.expression.u.varg_sequence.reg_alloc_saved_state);

        if (token_is (TOK_COMMA))
        {
          skip_token ();
        }
        else
        {
          current_token_must_be (TOK_CLOSE_BRACE);
        }

        JSP_FINISH_SUBEXPR ();
      }

      if (token_is (TOK_CLOSE_BRACE))
      {
        jsp_early_error_check_for_duplication_of_prop_names (is_strict_mode (), tok.loc);

        skip_token ();

        uint32_t list_len = state_p->u.expression.u.varg_sequence.list_length;
        vm_instr_counter_t header_pos = state_p->u.expression.u.varg_sequence.header_pos;

        state_p->u.expression.operand = tmp_operand ();

        rewrite_varg_header_set_args_count (state_p->u.expression.operand, list_len, header_pos);

        state_p->state = JSP_STATE_EXPR_MEMBER;
        state_p->is_list_in_process = false;
      }
      else
      {
        state_p->u.expression.u.varg_sequence.reg_alloc_saved_state = dumper_start_varg_code_sequence ();

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

        seek_token (start_pos);

        jsp_push_new_expr_state (expr_type, expr_type, true);
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_ARRAY_LITERAL)
    {
      JERRY_ASSERT (!state_p->is_completed);
      JERRY_ASSERT (state_p->is_list_in_process);

      if (is_subexpr_end)
      {
        dump_get_value_if_ref (substate_p, true);

        dump_varg (substate_p->u.expression.operand);

        JSP_FINISH_SUBEXPR ();

        state_p->u.expression.u.varg_sequence.list_length++;

        dumper_finish_varg_code_sequence (state_p->u.expression.u.varg_sequence.reg_alloc_saved_state);

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

          uint32_t list_len = state_p->u.expression.u.varg_sequence.list_length;
          vm_instr_counter_t header_pos = state_p->u.expression.u.varg_sequence.header_pos;

          state_p->u.expression.operand = tmp_operand ();
          rewrite_varg_header_set_args_count (state_p->u.expression.operand, list_len, header_pos);

          state_p->state = JSP_STATE_EXPR_MEMBER;
          state_p->is_list_in_process = false;
        }
        else if (token_is (TOK_COMMA))
        {
          while (token_is (TOK_COMMA))
          {
            skip_token ();

            vm_idx_t reg_alloc_saved_state = dumper_start_varg_code_sequence ();

            jsp_operand_t reg = tmp_operand ();
            dump_array_hole_assignment (reg);
            dump_varg (reg);

            state_p->u.expression.u.varg_sequence.list_length++;

            dumper_finish_varg_code_sequence (reg_alloc_saved_state);
          }
        }
        else
        {
          state_p->u.expression.u.varg_sequence.reg_alloc_saved_state = dumper_start_varg_code_sequence ();

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
            JERRY_ASSERT (state_p->u.expression.token_type == TOK_KW_NEW);
            JERRY_ASSERT (substate_p->state == JSP_STATE_EXPR_ASSIGNMENT);

            dump_get_value_if_ref (substate_p, true);

            dump_varg (substate_p->u.expression.operand);

            JSP_FINISH_SUBEXPR ();

            dumper_finish_varg_code_sequence (state_p->u.expression.u.varg_sequence.reg_alloc_saved_state);

            state_p->u.expression.u.varg_sequence.list_length++;

            if (token_is (TOK_CLOSE_PAREN))
            {
              state_p->u.expression.token_type = TOK_EMPTY;
              state_p->is_list_in_process = false;

              uint32_t list_len = state_p->u.expression.u.varg_sequence.list_length;
              vm_instr_counter_t header_pos = state_p->u.expression.u.varg_sequence.header_pos;

              state_p->u.expression.operand = jsp_finish_construct_dump (list_len, header_pos);
            }
            else
            {
              current_token_must_be (TOK_COMMA);

              jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);

              state_p->u.expression.u.varg_sequence.reg_alloc_saved_state = dumper_start_varg_code_sequence ();
            }

            skip_token ();
          }
          else if (state_p->u.expression.token_type == TOK_OPEN_PAREN)
          {
            JERRY_ASSERT (state_p->u.expression.operand.is_empty_operand ());

            state_p->u.expression.operand = substate_p->u.expression.operand;
            state_p->u.expression.prop_name_operand = substate_p->u.expression.prop_name_operand;
            state_p->is_value_based_reference = substate_p->is_value_based_reference;

            state_p->u.expression.token_type = TOK_EMPTY;

            JSP_FINISH_SUBEXPR ();

            current_token_must_be_check_and_skip_it (TOK_CLOSE_PAREN);
          }
          else if (state_p->u.expression.token_type == TOK_KW_NEW)
          {
            JERRY_ASSERT (substate_p->state == JSP_STATE_EXPR_MEMBER);
            JERRY_ASSERT (state_p->u.expression.operand.is_empty_operand ());
            JERRY_ASSERT (!substate_p->u.expression.operand.is_empty_operand ());

            state_p->u.expression.operand = substate_p->u.expression.operand;
            state_p->u.expression.prop_name_operand = substate_p->u.expression.prop_name_operand;
            state_p->is_value_based_reference = substate_p->is_value_based_reference;

            JSP_FINISH_SUBEXPR ();

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
              dump_get_value_for_prev_states (state_p);

              vm_instr_counter_t header_pos = jsp_start_construct_dump (state_p);

              state_p->is_list_in_process = true;
              state_p->u.expression.u.varg_sequence.list_length = 0;
              state_p->u.expression.u.varg_sequence.header_pos = header_pos;
              state_p->u.expression.u.varg_sequence.reg_alloc_saved_state = dumper_start_varg_code_sequence ();

              jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);
            }
            else
            {
              vm_instr_counter_t header_pos = jsp_start_construct_dump (state_p);

              state_p->u.expression.token_type = TOK_EMPTY;

              if (is_arg_list_implicit)
              {
                state_p->state = JSP_STATE_EXPR_MEMBER;
                state_p->is_completed = true;
              }

              state_p->u.expression.operand = jsp_finish_construct_dump (0, header_pos);
              state_p->u.expression.prop_name_operand = empty_operand ();
              state_p->is_value_based_reference = false;
            }
          }
          else
          {
            JERRY_ASSERT (state_p->u.expression.token_type == TOK_OPEN_SQUARE);
            state_p->u.expression.token_type = TOK_EMPTY;

            current_token_must_be_check_and_skip_it (TOK_CLOSE_SQUARE);

            dump_get_value_if_ref (substate_p, true);

            state_p->u.expression.prop_name_operand = substate_p->u.expression.operand;
            state_p->is_value_based_reference = true;

            JSP_FINISH_SUBEXPR ();
          }
        }
        else if (token_is (TOK_OPEN_SQUARE))
        {
          skip_token ();

          state_p->u.expression.token_type = TOK_OPEN_SQUARE;

          dump_get_value_if_ref (state_p, true);

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
        }
        else if (token_is (TOK_DOT))
        {
          skip_token ();

          lit_cpointer_t prop_name = jsp_get_prop_name_after_dot ();
          skip_token ();

          dump_get_value_if_ref (state_p, true);

          state_p->u.expression.prop_name_operand = tmp_operand ();
          dump_string_assignment (state_p->u.expression.prop_name_operand, prop_name);

          state_p->is_value_based_reference = true;
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
          JERRY_ASSERT (substate_p->state == JSP_STATE_EXPR_ASSIGNMENT);

          dump_get_value_if_ref (substate_p, true);

          dump_varg (substate_p->u.expression.operand);

          JSP_FINISH_SUBEXPR ();

          dumper_finish_varg_code_sequence (state_p->u.expression.u.varg_sequence.reg_alloc_saved_state);

          state_p->u.expression.u.varg_sequence.list_length++;

          if (token_is (TOK_CLOSE_PAREN))
          {
            state_p->is_list_in_process = false;

            uint32_t list_len = state_p->u.expression.u.varg_sequence.list_length;
            vm_instr_counter_t header_pos = state_p->u.expression.u.varg_sequence.header_pos;

            state_p->u.expression.operand = jsp_finish_call_dump (list_len, header_pos);
            state_p->u.expression.prop_name_operand = empty_operand ();
            state_p->is_value_based_reference = false;
          }
          else
          {
            current_token_must_be (TOK_COMMA);

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);

            state_p->u.expression.u.varg_sequence.reg_alloc_saved_state = dumper_start_varg_code_sequence ();
          }
        }
        else
        {
          JERRY_ASSERT (state_p->u.expression.token_type == TOK_OPEN_SQUARE);
          state_p->u.expression.token_type = TOK_EMPTY;

          current_token_must_be (TOK_CLOSE_SQUARE);

          dump_get_value_if_ref (substate_p, true);
          state_p->u.expression.prop_name_operand = substate_p->u.expression.operand;
          state_p->is_value_based_reference = true;

          JSP_FINISH_SUBEXPR ();
        }

        skip_token ();
      }
      else
      {
        if (token_is (TOK_OPEN_PAREN))
        {
          skip_token ();

          dump_get_value_for_prev_states (state_p);

          vm_instr_counter_t header_pos = jsp_start_call_dump (state_p);

          if (token_is (TOK_CLOSE_PAREN))
          {
            skip_token ();

            state_p->u.expression.operand = jsp_finish_call_dump (0, header_pos);
            state_p->u.expression.prop_name_operand = empty_operand ();
            state_p->is_value_based_reference = false;
          }
          else
          {
            state_p->is_list_in_process = true;
            state_p->u.expression.u.varg_sequence.list_length = 0;
            state_p->u.expression.u.varg_sequence.header_pos = header_pos;
            state_p->u.expression.u.varg_sequence.reg_alloc_saved_state = dumper_start_varg_code_sequence ();

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);
          }
        }
        else if (token_is (TOK_OPEN_SQUARE))
        {
          skip_token ();

          state_p->u.expression.token_type = TOK_OPEN_SQUARE;
          dump_get_value_if_ref (state_p, false);

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
        }
        else if (token_is (TOK_DOT))
        {
          skip_token ();

          lit_cpointer_t prop_name = jsp_get_prop_name_after_dot ();
          skip_token ();

          dump_get_value_if_ref (state_p, false);

          state_p->u.expression.prop_name_operand = tmp_operand ();
          dump_string_assignment (state_p->u.expression.prop_name_operand, prop_name);

          state_p->is_value_based_reference = true;
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
        jsp_token_type_t tt = state_p->u.expression.token_type;
        JERRY_ASSERT (tt >= TOKEN_TYPE__ASSIGNMENTS_BEGIN && tt <= TOKEN_TYPE__ASSIGNMENTS_END);

        dump_get_value_for_prev_states (state_p);
        dump_get_value_if_ref (substate_p, true);

        if (tt == TOK_EQ)
        {
          if (state_p->is_need_retval)
          {
            dump_get_value_if_ref (substate_p, false);
          }

          if (state_p->is_value_based_reference)
          {
            dump_prop_setter (state_p->u.expression.operand,
                              state_p->u.expression.prop_name_operand,
                              substate_p->u.expression.operand);

            state_p->u.expression.prop_name_operand = empty_operand ();
            state_p->is_value_based_reference = false;
          }
          else
          {
            dump_variable_assignment (state_p->u.expression.operand, substate_p->u.expression.operand);
          }

          state_p->u.expression.operand = substate_p->u.expression.operand;

          if (state_p->is_need_retval)
          {
            JERRY_ASSERT (state_p->u.expression.operand.is_register_operand ());
          }
        }
        else
        {
          vm_op_t opcode;

          if (tt == TOK_MULT_EQ)
          {
            opcode = VM_OP_MULTIPLICATION;
          }
          else if (tt == TOK_DIV_EQ)
          {
            opcode = VM_OP_DIVISION;
          }
          else if (tt == TOK_MOD_EQ)
          {
            opcode = VM_OP_REMAINDER;
          }
          else if (tt == TOK_PLUS_EQ)
          {
            opcode = VM_OP_ADDITION;
          }
          else if (tt == TOK_MINUS_EQ)
          {
            opcode = VM_OP_SUBSTRACTION;
          }
          else if (tt == TOK_LSHIFT_EQ)
          {
            opcode = VM_OP_B_SHIFT_LEFT;
          }
          else if (tt == TOK_RSHIFT_EQ)
          {
            opcode = VM_OP_B_SHIFT_RIGHT;
          }
          else if (tt == TOK_RSHIFT_EX_EQ)
          {
            opcode = VM_OP_B_SHIFT_URIGHT;
          }
          else if (tt == TOK_AND_EQ)
          {
            opcode = VM_OP_B_AND;
          }
          else if (tt == TOK_XOR_EQ)
          {
            opcode = VM_OP_B_XOR;
          }
          else
          {
            JERRY_ASSERT (tt == TOK_OR_EQ);

            opcode = VM_OP_B_OR;
          }

          if (state_p->is_value_based_reference)
          {
            jsp_operand_t reg = tmp_operand ();

            dump_prop_getter (reg, state_p->u.expression.operand, state_p->u.expression.prop_name_operand);

            dump_binary_op (opcode, reg, reg, substate_p->u.expression.operand);

            dump_prop_setter (state_p->u.expression.operand,
                              state_p->u.expression.prop_name_operand,
                              reg);

            state_p->u.expression.operand = reg;
            state_p->u.expression.prop_name_operand = empty_operand ();
            state_p->is_value_based_reference = false;
          }
          else if (state_p->is_need_retval)
          {
            jsp_operand_t reg = tmp_operand ();

            dump_binary_op (opcode, reg, state_p->u.expression.operand, substate_p->u.expression.operand);

            dump_variable_assignment (state_p->u.expression.operand, reg);

            state_p->u.expression.operand = reg;
          }
          else
          {
            dump_binary_op (opcode, state_p->u.expression.operand,
                            state_p->u.expression.operand,
                            substate_p->u.expression.operand);

            state_p->u.expression.operand = empty_operand ();
          }
        }

        state_p->state = JSP_STATE_EXPR_ASSIGNMENT;
        state_p->u.expression.token_type = TOK_EMPTY;
        state_p->is_completed = true;

        JSP_FINISH_SUBEXPR ();
      }
      else
      {
        JERRY_ASSERT (state_p->u.expression.token_type == TOK_EMPTY);

        if (token_is (TOK_DOUBLE_PLUS)
            && !lexer_is_preceded_by_newlines (tok))
        {
          const jsp_operand_t reg = tmp_operand ();

          if (state_p->is_value_based_reference)
          {
            const jsp_operand_t val = tmp_operand ();

            dump_prop_getter (val, state_p->u.expression.operand, state_p->u.expression.prop_name_operand);

            dump_unary_op (VM_OP_POST_INCR, reg, val);

            dump_prop_setter (state_p->u.expression.operand, state_p->u.expression.prop_name_operand, val);

            state_p->u.expression.operand = reg;
            state_p->u.expression.prop_name_operand = empty_operand ();
            state_p->is_value_based_reference = false;
          }
          else if (state_p->u.expression.operand.is_identifier_operand ())
          {
            jsp_early_error_check_for_eval_and_arguments_in_strict_mode (state_p->u.expression.operand,
                                                                         is_strict_mode (),
                                                                         tok.loc);

            dump_unary_op (VM_OP_POST_INCR, reg, state_p->u.expression.operand);

            state_p->u.expression.operand = reg;
          }
          else
          {
            PARSE_ERROR (JSP_EARLY_ERROR_REFERENCE, "Invalid left-hand-side expression", tok.loc);
          }

          state_p->state = JSP_STATE_EXPR_UNARY;
          JERRY_ASSERT (state_p->is_completed);

          skip_token ();
        }
        else if (token_is (TOK_DOUBLE_MINUS)
                 && !lexer_is_preceded_by_newlines (tok))
        {
          const jsp_operand_t reg = tmp_operand ();

          if (state_p->is_value_based_reference)
          {
            const jsp_operand_t val = tmp_operand ();

            dump_prop_getter (val, state_p->u.expression.operand, state_p->u.expression.prop_name_operand);

            dump_unary_op (VM_OP_POST_DECR, reg, val);

            dump_prop_setter (state_p->u.expression.operand, state_p->u.expression.prop_name_operand, val);

            state_p->u.expression.operand = reg;
            state_p->u.expression.prop_name_operand = empty_operand ();
            state_p->is_value_based_reference = false;
          }
          else if (state_p->u.expression.operand.is_identifier_operand ())
          {
            jsp_early_error_check_for_eval_and_arguments_in_strict_mode (state_p->u.expression.operand,
                                                                         is_strict_mode (),
                                                                         tok.loc);

            dump_unary_op (VM_OP_POST_DECR, reg, state_p->u.expression.operand);

            state_p->u.expression.operand = reg;
          }
          else
          {
            PARSE_ERROR (JSP_EARLY_ERROR_REFERENCE, "Invalid left-hand-side expression", tok.loc);
          }

          state_p->state = JSP_STATE_EXPR_UNARY;
          JERRY_ASSERT (state_p->is_completed);

          skip_token ();
        }
        else
        {
          jsp_token_type_t tt = lexer_get_token_type (tok);

          if (tt >= TOKEN_TYPE__ASSIGNMENTS_BEGIN && tt <= TOKEN_TYPE__ASSIGNMENTS_END)
          {
            if (!state_p->is_value_based_reference)
            {
              if (!state_p->u.expression.operand.is_identifier_operand ())
              {
                PARSE_ERROR (JSP_EARLY_ERROR_REFERENCE, "Invalid left-hand-side expression", tok.loc);
              }
              else
              {
                jsp_early_error_check_for_eval_and_arguments_in_strict_mode (state_p->u.expression.operand,
                                                                             is_strict_mode (),
                                                                             tok.loc);
              }
            }

            /* skip the assignment operator */
            skip_token ();
            state_p->u.expression.token_type = tt;

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, in_allowed);
          }
          else
          {
            state_p->state = JSP_STATE_EXPR_UNARY;
          }
        }
      }
    }
    else if (state_p->state > JSP_STATE_EXPR__SIMPLE_BEGIN
             && state_p->state < JSP_STATE_EXPR__SIMPLE_END)
    {
      JERRY_STATIC_ASSERT (JSP_STATE_EXPR_MULTIPLICATIVE == JSP_STATE_EXPR_UNARY + 1u);
      JERRY_STATIC_ASSERT (JSP_STATE_EXPR_ADDITIVE == JSP_STATE_EXPR_MULTIPLICATIVE + 1u);
      JERRY_STATIC_ASSERT (JSP_STATE_EXPR_SHIFT == JSP_STATE_EXPR_ADDITIVE + 1u);
      JERRY_STATIC_ASSERT (JSP_STATE_EXPR_RELATIONAL == JSP_STATE_EXPR_SHIFT + 1u);
      JERRY_STATIC_ASSERT (JSP_STATE_EXPR_EQUALITY == JSP_STATE_EXPR_RELATIONAL + 1u);
      JERRY_STATIC_ASSERT (JSP_STATE_EXPR_BITWISE_AND == JSP_STATE_EXPR_EQUALITY + 1u);
      JERRY_STATIC_ASSERT (JSP_STATE_EXPR_BITWISE_XOR == JSP_STATE_EXPR_BITWISE_AND + 1u);
      JERRY_STATIC_ASSERT (JSP_STATE_EXPR_BITWISE_OR == JSP_STATE_EXPR_BITWISE_XOR + 1u);

      if (state_p->is_completed)
      {
        if (state_p->state == JSP_STATE_EXPR_BITWISE_OR)
        {
          state_p->state = JSP_STATE_EXPR_LOGICAL_AND;

          state_p->u.expression.u.logical_and.rewrite_chain = MAX_OPCODES;
        }
        else
        {
          JERRY_ASSERT (state_p->state != state_p->req_state);
          JERRY_ASSERT (state_p->state == JSP_STATE_EXPR_UNARY);

          state_p->state = (jsp_state_expr_t) (state_p->state + 1u);
        }

        state_p->is_completed = false;
      }
      else if (is_subexpr_end)
      {
        bool is_combined_with_assignment;

        if (state_p->state == JSP_STATE_EXPR_UNARY)
        {
          is_combined_with_assignment = jsp_dump_unary_op (state_p, substate_p);
        }
        else
        {
          is_combined_with_assignment = jsp_dump_binary_op (state_p, substate_p);
        }

        JSP_FINISH_SUBEXPR ();

        if (is_combined_with_assignment)
        {
          JSP_ASSIGNMENT_EXPR_COMBINE ();
        }
      }
      else
      {
        JERRY_ASSERT (!state_p->is_completed);


        jsp_state_expr_t new_state, subexpr_type;

        bool is_simple = true;

        jsp_token_type_t tt = lexer_get_token_type (tok);

        if (tt >= TOKEN_TYPE__MULTIPLICATIVE_BEGIN && tt <= TOKEN_TYPE__MULTIPLICATIVE_END)
        {
          JERRY_ASSERT (state_p->state >= JSP_STATE_EXPR_UNARY && state_p->state <= JSP_STATE_EXPR_MULTIPLICATIVE);

          new_state = JSP_STATE_EXPR_MULTIPLICATIVE;
          subexpr_type = JSP_STATE_EXPR_UNARY;
        }
        else if (tt >= TOKEN_TYPE__ADDITIVE_BEGIN && tt <= TOKEN_TYPE__ADDITIVE_END)
        {
          JERRY_ASSERT (state_p->state >= JSP_STATE_EXPR_UNARY && state_p->state <= JSP_STATE_EXPR_ADDITIVE);

          new_state = JSP_STATE_EXPR_ADDITIVE;
          subexpr_type = JSP_STATE_EXPR_MULTIPLICATIVE;
        }
        else if (tt >= TOKEN_TYPE__SHIFT_BEGIN && tt <= TOKEN_TYPE__SHIFT_END)
        {
          JERRY_ASSERT (state_p->state >= JSP_STATE_EXPR_UNARY && state_p->state <= JSP_STATE_EXPR_SHIFT);

          new_state = JSP_STATE_EXPR_SHIFT;
          subexpr_type = JSP_STATE_EXPR_ADDITIVE;
        }
        else if ((tt >= TOKEN_TYPE__RELATIONAL_BEGIN && tt <= TOKEN_TYPE__RELATIONAL_END)
                 || tt == TOK_KW_INSTANCEOF
                 || (in_allowed && tt == TOK_KW_IN))
        {
          JERRY_ASSERT (state_p->state >= JSP_STATE_EXPR_UNARY && state_p->state <= JSP_STATE_EXPR_RELATIONAL);

          new_state = JSP_STATE_EXPR_RELATIONAL;
          subexpr_type = JSP_STATE_EXPR_SHIFT;
        }
        else if (tt >= TOKEN_TYPE__EQUALITY_BEGIN && tt <= TOKEN_TYPE__EQUALITY_END)
        {
          JERRY_ASSERT (state_p->state >= JSP_STATE_EXPR_UNARY && state_p->state <= JSP_STATE_EXPR_EQUALITY);

          new_state = JSP_STATE_EXPR_EQUALITY;
          subexpr_type = JSP_STATE_EXPR_RELATIONAL;
        }
        else if (tt == TOK_AND)
        {
          JERRY_ASSERT (state_p->state >= JSP_STATE_EXPR_UNARY && state_p->state <= JSP_STATE_EXPR_BITWISE_AND);

          new_state = JSP_STATE_EXPR_BITWISE_AND;
          subexpr_type = JSP_STATE_EXPR_EQUALITY;
        }
        else if (tt == TOK_XOR)
        {
          JERRY_ASSERT (state_p->state >= JSP_STATE_EXPR_UNARY && state_p->state <= JSP_STATE_EXPR_BITWISE_XOR);

          new_state = JSP_STATE_EXPR_BITWISE_XOR;
          subexpr_type = JSP_STATE_EXPR_BITWISE_AND;
        }
        else if (tt == TOK_OR)
        {
          JERRY_ASSERT (state_p->state >= JSP_STATE_EXPR_UNARY && state_p->state <= JSP_STATE_EXPR_BITWISE_OR);

          new_state = JSP_STATE_EXPR_BITWISE_OR;
          subexpr_type = JSP_STATE_EXPR_BITWISE_XOR;
        }
        else
        {
          is_simple = false;
        }

        if (!is_simple && state_p->req_state >= JSP_STATE_EXPR_LOGICAL_AND)
        {
          state_p->state = JSP_STATE_EXPR_LOGICAL_AND;
          state_p->u.expression.u.logical_and.rewrite_chain = MAX_OPCODES;
        }
        else
        {
          JERRY_ASSERT (is_simple || state_p->req_state < JSP_STATE_EXPR__SIMPLE_END);

          if (!is_simple || state_p->req_state < new_state)
          {
            state_p->state = state_p->req_state;

            state_p->is_completed = true;
          }
          else
          {
            skip_token ();

            state_p->state = new_state;
            state_p->u.expression.token_type = tt;

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, subexpr_type, in_allowed);
          }
        }
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_LOGICAL_AND)
    {
      if (state_p->is_completed)
      {
        /* propagate to LogicalOrExpression */
        state_p->state = JSP_STATE_EXPR_LOGICAL_OR;

        state_p->u.expression.u.logical_or.rewrite_chain = MAX_OPCODES;

        state_p->is_completed = false;
      }
      else
      {
        if (is_subexpr_end)
        {
          dump_get_value_if_ref (state_p, true);
          dump_get_value_if_ref (substate_p, true);

          JERRY_ASSERT (state_p->u.expression.token_type == TOK_DOUBLE_AND);

          JERRY_ASSERT (state_p->u.expression.operand.is_register_operand ());

          dump_variable_assignment (state_p->u.expression.operand, substate_p->u.expression.operand);

          state_p->u.expression.token_type = TOK_EMPTY;

          JSP_FINISH_SUBEXPR ();
        }
        else
        {
          JERRY_ASSERT (state_p->u.expression.token_type == TOK_EMPTY);

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

              state_p->u.expression.u.logical_and.rewrite_chain = MAX_OPCODES;

              JERRY_ASSERT (!state_p->is_fixed_ret_operand);

              jsp_operand_t ret = tmp_operand ();

              dump_get_value_if_ref (state_p, true);

              dump_variable_assignment (ret, state_p->u.expression.operand);

              state_p->is_fixed_ret_operand = true;
              state_p->u.expression.operand = ret;
            }

            JERRY_ASSERT (state_p->is_complex_production);

            jsp_add_conditional_jump_to_rewrite_chain (&state_p->u.expression.u.logical_and.rewrite_chain,
                                                       true, state_p->u.expression.operand);

            state_p->u.expression.token_type = TOK_DOUBLE_AND;

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_BITWISE_OR, in_allowed);
          }
          else
          {
            /* end of LogicalAndExpression */
            JERRY_ASSERT (state_p->u.expression.token_type == TOK_EMPTY);

            jsp_rewrite_jumps_chain (&state_p->u.expression.u.logical_and.rewrite_chain,
                                     dumper_get_current_instr_counter ());

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

          dump_get_value_if_ref (state_p, true);

          vm_instr_counter_t conditional_check_pos = dump_conditional_check_for_rewrite (state_p->u.expression.operand);
          state_p->u.expression.u.conditional.conditional_check_pos = conditional_check_pos;

          state_p->u.expression.token_type = TOK_QUERY;

          if (!state_p->is_fixed_ret_operand)
          {
            state_p->is_fixed_ret_operand = true;
            state_p->u.expression.operand = tmp_operand ();
          }

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
          dump_get_value_if_ref (substate_p, true);

          JERRY_ASSERT (state_p->u.expression.token_type == TOK_DOUBLE_OR);

          JERRY_ASSERT (state_p->u.expression.operand.is_register_operand ());
          dump_variable_assignment (state_p->u.expression.operand, substate_p->u.expression.operand);

          state_p->u.expression.token_type = TOK_EMPTY;

          JSP_FINISH_SUBEXPR ();
        }
        else
        {
          JERRY_ASSERT (state_p->u.expression.token_type == TOK_EMPTY);

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

              state_p->u.expression.u.logical_or.rewrite_chain = MAX_OPCODES;

              jsp_operand_t ret;

              if (state_p->is_fixed_ret_operand)
              {
                JERRY_ASSERT (state_p->u.expression.operand.is_register_operand ());

                ret = state_p->u.expression.operand;
              }
              else
              {
                ret = tmp_operand ();

                dump_get_value_if_ref (state_p, true);

                dump_variable_assignment (ret, state_p->u.expression.operand);

                state_p->is_fixed_ret_operand = true;

                state_p->u.expression.operand = ret;
              }
            }

            JERRY_ASSERT (state_p->is_complex_production);

            jsp_add_conditional_jump_to_rewrite_chain (&state_p->u.expression.u.logical_or.rewrite_chain,
                                                       false, state_p->u.expression.operand);

            state_p->u.expression.token_type = TOK_DOUBLE_OR;

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_LOGICAL_AND, in_allowed);
          }
          else
          {
            /* end of LogicalOrExpression */
            JERRY_ASSERT (state_p->u.expression.token_type == TOK_EMPTY);

            jsp_rewrite_jumps_chain (&state_p->u.expression.u.logical_or.rewrite_chain,
                                     dumper_get_current_instr_counter ());

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
      JERRY_ASSERT (state_p->u.expression.token_type == TOK_EMPTY);

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
      if (state_p->u.expression.token_type == TOK_QUERY)
      {
        current_token_must_be_check_and_skip_it (TOK_COLON);

        JERRY_ASSERT (state_p->is_fixed_ret_operand);
        JERRY_ASSERT (state_p->u.expression.operand.is_register_operand ());
        JERRY_ASSERT (substate_p->state == JSP_STATE_EXPR_ASSIGNMENT);

        dump_get_value_if_ref (substate_p, true);

        dump_variable_assignment (state_p->u.expression.operand, substate_p->u.expression.operand);

        JSP_FINISH_SUBEXPR ();

        state_p->u.expression.u.conditional.jump_to_end_pos = dump_jump_to_end_for_rewrite ();

        rewrite_conditional_check (state_p->u.expression.u.conditional.conditional_check_pos);

        state_p->u.expression.token_type = TOK_COLON;

        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, in_allowed);
      }
      else
      {
        JERRY_ASSERT (state_p->u.expression.token_type == TOK_COLON);

        JERRY_ASSERT (state_p->is_fixed_ret_operand);
        JERRY_ASSERT (state_p->u.expression.operand.is_register_operand ());
        JERRY_ASSERT (substate_p->state == JSP_STATE_EXPR_ASSIGNMENT);

        dump_get_value_if_ref (substate_p, true);

        dump_variable_assignment (state_p->u.expression.operand, substate_p->u.expression.operand);

        JSP_FINISH_SUBEXPR ();

        rewrite_jump_to_end (state_p->u.expression.u.conditional.jump_to_end_pos);

        state_p->u.expression.token_type = TOK_EMPTY;
        state_p->is_fixed_ret_operand = false;

        state_p->state = JSP_STATE_EXPR_ASSIGNMENT;
        state_p->is_completed = true;
      }
    }
    else if (state_p->state == JSP_STATE_EXPR_EXPRESSION)
    {
      /* ECMA-262 v5, 11.14 */
      JERRY_ASSERT (state_p->state == JSP_STATE_EXPR_EXPRESSION);

      if (is_subexpr_end)
      {
        JERRY_ASSERT (state_p->u.expression.token_type == TOK_COMMA);

        /*
         * The operand should be already evaluated
         *
         * See also:
         *          11.14, step 2
         */
        JERRY_ASSERT (!state_p->is_value_based_reference
                      && state_p->u.expression.operand.is_register_operand ());

        /* evaluating, if reference */
        dump_get_value_if_ref (substate_p, false);

        state_p->u.expression.operand = substate_p->u.expression.operand;

        JSP_FINISH_SUBEXPR ();
      }
      else
      {
        JERRY_ASSERT (!state_p->is_completed);

        if (token_is (TOK_COMMA))
        {
          skip_token ();

          JERRY_ASSERT (!token_is (TOK_COMMA));

          state_p->u.expression.token_type = TOK_COMMA;

          /* ECMA-262 v5, 11.14, step 2 */
          dump_get_value_if_ref (state_p, false);

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, in_allowed);
        }
        else
        {
          state_p->is_completed = true;
        }
      }
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
        jsp_state_top ()->req_state = JSP_STATE_STAT_STATEMENT_LIST;
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
        state_p->u.statement.u.iterational.continues_rewrite_chain = MAX_OPCODES;
        state_p->u.statement.u.iterational.continue_tgt_oc = MAX_OPCODES;

        if (token_is (TOK_KW_DO))
        {
          state_p->u.statement.u.iterational.u.loop_do_while.next_iter_tgt_pos = dumper_set_next_iteration_target ();
          skip_token ();

          JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_STAT_DO_WHILE);
        }
        else if (token_is (TOK_KW_WHILE))
        {
          skip_token ();

          state_p->u.statement.u.iterational.u.loop_while.u.cond_expr_start_loc = tok.loc;
          jsp_skip_braces (TOK_OPEN_PAREN);

          state_p->u.statement.u.iterational.u.loop_while.jump_to_end_pos = dump_jump_to_end_for_rewrite ();

          state_p->u.statement.u.iterational.u.loop_while.next_iter_tgt_pos = dumper_set_next_iteration_target ();

          skip_token ();

          JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_STAT_WHILE);
        }
        else
        {
          current_token_must_be_check_and_skip_it (TOK_KW_FOR);

          current_token_must_be (TOK_OPEN_PAREN);

          locus for_open_paren_loc, for_body_statement_loc;

          for_open_paren_loc = tok.loc;

          jsp_skip_braces (TOK_OPEN_PAREN);
          skip_token ();

          for_body_statement_loc = tok.loc;

          seek_token (for_open_paren_loc);

          bool is_plain_for = jsp_find_next_token_before_the_locus (TOK_SEMICOLON,
                                                                    for_body_statement_loc,
                                                                    true);
          seek_token (for_open_paren_loc);

          if (is_plain_for)
          {
            state_p->u.statement.u.iterational.u.loop_for.u1.body_loc = for_body_statement_loc;

            current_token_must_be_check_and_skip_it (TOK_OPEN_PAREN);

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

                jsp_state_top ()->is_need_retval = false;
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
            current_token_must_be_check_and_skip_it (TOK_OPEN_PAREN);

            // Save Iterator location
            state_p->u.statement.u.iterational.u.loop_for_in.u.iterator_expr_loc = tok.loc;

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
            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
            state_p->state = JSP_STATE_STAT_FOR_IN;
          }
        }
      }
      else if (token_is (TOK_KW_SWITCH))
      {
        skip_token ();

        parse_expression_inside_parens_begin ();
        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
        state_p->state = JSP_STATE_STAT_SWITCH;
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

        jsp_state_t *prev_state_p = jsp_get_prev_state (state_p);

        if (prev_state_p->state == JSP_STATE_STAT_STATEMENT_LIST)
        {
          prev_state_p->is_stmt_list_control_flow_exit_stmt_occured = true;
        }

        jsp_state_t *labelled_stmt_p;
        bool is_simply_jumpable = true;

        if (!lexer_is_preceded_by_newlines (tok) && token_is (TOK_NAME))
        {
          /* break or continue on a label */
          labelled_stmt_p = jsp_find_named_label (token_data_as_lit_cp (), &is_simply_jumpable);

          if (labelled_stmt_p == NULL)
          {
            EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Label not found");
          }

          skip_token ();
        }
        else
        {
          labelled_stmt_p = jsp_find_unnamed_label (is_break, &is_simply_jumpable);

          if (labelled_stmt_p == NULL)
          {
            if (is_break)
            {
              EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "No corresponding statement for the break");
            }
            else
            {
              EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "No corresponding statement for the continue");
            }
          }
        }

        insert_semicolon ();

        JERRY_ASSERT (labelled_stmt_p != NULL);

        vm_instr_counter_t *rewrite_chain_p;
        if (is_break)
        {
          rewrite_chain_p = &labelled_stmt_p->u.statement.breaks_rewrite_chain;
        }
        else
        {
          rewrite_chain_p = &labelled_stmt_p->u.statement.u.iterational.continues_rewrite_chain;
        }

        if (is_simply_jumpable)
        {
          jsp_add_simple_jump_to_rewrite_chain (rewrite_chain_p);
        }
        else
        {
          jsp_add_nested_jump_to_rewrite_chain (rewrite_chain_p);
        }

        JSP_COMPLETE_STATEMENT_PARSE ();
      }
      else if (token_is (TOK_KW_RETURN))
      {
        if (dumper_get_scope ()->type != SCOPE_TYPE_FUNCTION)
        {
          EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Return is illegal");
        }

        jsp_state_t *prev_state_p = jsp_get_prev_state (state_p);

        if (prev_state_p->state == JSP_STATE_STAT_STATEMENT_LIST)
        {
          prev_state_p->is_stmt_list_control_flow_exit_stmt_occured = true;
        }

        skip_token ();

        if (!token_is (TOK_SEMICOLON)
            && !lexer_is_preceded_by_newlines (tok)
            && !token_is (TOK_CLOSE_BRACE))
        {
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
          state_p->state = JSP_STATE_STAT_RETURN;
        }
        else
        {
          dump_ret ();
          JSP_COMPLETE_STATEMENT_PARSE ();
        }
      }
      else if (token_is (TOK_KW_TRY))
      {
        skip_token ();

        scopes_tree_set_contains_try (dumper_get_scope ());

        state_p->u.statement.u.try_statement.try_pos = dump_try_for_rewrite ();

        current_token_must_be_check_and_skip_it (TOK_OPEN_BRACE);

        state_p->is_simply_jumpable_border = true;

        state_p->state = JSP_STATE_STAT_TRY;
        jsp_start_statement_parse (JSP_STATE_STAT_BLOCK);
        jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT_LIST);
        jsp_state_top ()->req_state = JSP_STATE_STAT_STATEMENT_LIST;
      }
      else if (token_is (TOK_KW_WITH))
      {
        skip_token ();

        if (is_strict_mode ())
        {
          EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "'with' expression is not allowed in strict mode.");
        }

        parse_expression_inside_parens_begin();
        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
        state_p->state = JSP_STATE_STAT_WITH;
      }
      else if (token_is (TOK_KW_THROW))
      {
        skip_token ();

        jsp_state_t *prev_state_p = jsp_get_prev_state (state_p);

        if (prev_state_p->state == JSP_STATE_STAT_STATEMENT_LIST)
        {
          prev_state_p->is_stmt_list_control_flow_exit_stmt_occured = true;
        }

        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
        state_p->state = JSP_STATE_STAT_THROW;
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
        jsp_state_top ()->req_state = JSP_STATE_SOURCE_ELEMENTS;
      }
      else
      {
        bool is_expression = true;

        if (token_is (TOK_NAME))  // LabelledStatement or ExpressionStatement
        {
          const token temp = tok;
          skip_token ();
          if (token_is (TOK_COLON))
          {
            skip_token ();

            lit_cpointer_t name_cp;
            name_cp.packed_value = temp.uid;

            bool is_simply_jumpable;
            jsp_state_t *named_label_state_p = jsp_find_named_label (name_cp, &is_simply_jumpable);

            if (named_label_state_p != NULL)
            {
              EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Label is duplicated");
            }

            state_p->state = JSP_STATE_STAT_NAMED_LABEL;
            state_p->u.named_label.name_cp = name_cp;

            jsp_start_statement_parse (JSP_STATE_STAT_EMPTY);

            is_expression = false;
          }
          else
          {
            seek_token (temp.loc);
          }
        }

        if (is_expression)
        {
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);

          if (dumper_get_scope ()->type != SCOPE_TYPE_EVAL)
          {
            jsp_state_top ()->is_need_retval = false;
          }

          state_p->state = JSP_STATE_STAT_EXPRESSION;
        }
      }
    }
    else if (state_p->state == JSP_STATE_STAT_BLOCK)
    {
      JERRY_ASSERT (is_stmt_list_end);

      jsp_state_t *prev_state_p = jsp_get_prev_state (state_p);

      if (prev_state_p->state == JSP_STATE_STAT_STATEMENT_LIST)
      {
        prev_state_p->is_stmt_list_control_flow_exit_stmt_occured = is_stmt_list_control_flow_exit_stmt_occured;
      }

      current_token_must_be_check_and_skip_it (TOK_CLOSE_BRACE);

      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else if (state_p->state == JSP_STATE_STAT_IF_BRANCH_START)
    {
      if (is_subexpr_end) // Finished parsing condition
      {
        parse_expression_inside_parens_end ();

        dump_get_value_if_ref (substate_p, true);

        jsp_operand_t cond = substate_p->u.expression.operand;

        state_p->u.statement.u.if_statement.conditional_check_pos = dump_conditional_check_for_rewrite (cond);

        JSP_FINISH_SUBEXPR ();

        JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_STAT_IF_BRANCH_START);
      }
      else
      {
        if (token_is (TOK_KW_ELSE))
        {
          skip_token ();

          state_p->u.statement.u.if_statement.jump_to_end_pos = dump_jump_to_end_for_rewrite ();
          rewrite_conditional_check (state_p->u.statement.u.if_statement.conditional_check_pos);

          JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_STAT_IF_BRANCH_END);
        }
        else
        {
          rewrite_conditional_check (state_p->u.statement.u.if_statement.conditional_check_pos);

          JSP_COMPLETE_STATEMENT_PARSE ();
        }
      }
    }
    else if (state_p->state == JSP_STATE_STAT_IF_BRANCH_END)
    {
      rewrite_jump_to_end (state_p->u.statement.u.if_statement.jump_to_end_pos);

      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else if (state_p->state == JSP_STATE_STAT_STATEMENT_LIST)
    {
      if (is_subexpr_end)
      {
        JSP_FINISH_SUBEXPR ();
      }

      while (token_is (TOK_SEMICOLON))
      {
        skip_token ();
      }

      if (token_is (TOK_CLOSE_BRACE)
          || (token_is (TOK_KW_CASE) || token_is (TOK_KW_DEFAULT)))
      {
        state_p->is_completed = true;
      }
      else
      {
        jsp_start_statement_parse (JSP_STATE_STAT_EMPTY);
      }
    }
    else if (state_p->state == JSP_STATE_STAT_VAR_DECL)
    {
      skip_token ();

      locus name_loc = tok.loc;

      current_token_must_be (TOK_NAME);

      const lit_cpointer_t lit_cp = token_data_as_lit_cp ();
      const jsp_operand_t name = literal_operand (lit_cp);

      skip_token ();

      jsp_early_error_check_for_eval_and_arguments_in_strict_mode (name, is_strict_mode (), name_loc);

      if (!scopes_tree_variable_declaration_exists (dumper_get_scope (), lit_cp))
      {
        dump_variable_declaration (lit_cp);
      }

      if (token_is (TOK_EQ))
      {
        seek_token (name_loc);

        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);

        jsp_state_top ()->is_need_retval = false;
      }

      state_p->state = JSP_STATE_STAT_VAR_DECL_FINISH;
    }
    else if (state_p->state == JSP_STATE_STAT_VAR_DECL_FINISH)
    {
      if (is_subexpr_end)
      {
        JSP_FINISH_SUBEXPR ();
      }

      if (!token_is (TOK_COMMA))
      {
        JSP_COMPLETE_STATEMENT_PARSE ();

        if (state_p->var_decl)
        {
          insert_semicolon ();
        }
      }
      else
      {
        state_p->state = JSP_STATE_STAT_VAR_DECL;
      }
    }
    else if (state_p->state == JSP_STATE_STAT_DO_WHILE)
    {
      if (is_subexpr_end)
      {
        parse_expression_inside_parens_end ();

        const jsp_operand_t cond = substate_p->u.expression.operand;

        JSP_FINISH_SUBEXPR ();

        dump_continue_iterations_check (state_p->u.statement.u.iterational.u.loop_do_while.next_iter_tgt_pos, cond);

        state_p->state = JSP_STATE_STAT_ITER_FINISH;
      }
      else
      {
        assert_keyword (TOK_KW_WHILE);
        skip_token ();

        JERRY_ASSERT (state_p->u.statement.u.iterational.continue_tgt_oc == MAX_OPCODES);
        state_p->u.statement.u.iterational.continue_tgt_oc = dumper_get_current_instr_counter ();

        parse_expression_inside_parens_begin ();
        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
      }
    }
    else if (state_p->state == JSP_STATE_STAT_WHILE)
    {
      if (is_subexpr_end)
      {
        parse_expression_inside_parens_end ();

        const jsp_operand_t cond = substate_p->u.expression.operand;

        JSP_FINISH_SUBEXPR ();

        dump_continue_iterations_check (state_p->u.statement.u.iterational.u.loop_while.next_iter_tgt_pos, cond);

        seek_token (state_p->u.statement.u.iterational.u.loop_while.u.end_loc);

        state_p->state = JSP_STATE_STAT_ITER_FINISH;
      }
      else
      {
        JERRY_ASSERT (state_p->u.statement.u.iterational.continue_tgt_oc == MAX_OPCODES);
        state_p->u.statement.u.iterational.continue_tgt_oc = dumper_get_current_instr_counter ();

        rewrite_jump_to_end (state_p->u.statement.u.iterational.u.loop_while.jump_to_end_pos);

        const locus end_loc = tok.loc;

        seek_token (state_p->u.statement.u.iterational.u.loop_while.u.cond_expr_start_loc);

        state_p->u.statement.u.iterational.u.loop_while.u.end_loc = end_loc;

        parse_expression_inside_parens_begin ();
        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
      }
    }
    else if (state_p->state == JSP_STATE_STAT_FOR_INIT_END)
    {
      if (is_subexpr_end)
      {
        JSP_FINISH_SUBEXPR ();
      }

      // Jump -> ConditionCheck
      state_p->u.statement.u.iterational.u.loop_for.jump_to_end_pos = dump_jump_to_end_for_rewrite ();

      state_p->u.statement.u.iterational.u.loop_for.next_iter_tgt_pos = dumper_set_next_iteration_target ();

      current_token_must_be_check_and_skip_it (TOK_SEMICOLON);

      locus for_body_statement_loc = state_p->u.statement.u.iterational.u.loop_for.u1.body_loc;

      // Save Condition locus
      state_p->u.statement.u.iterational.u.loop_for.u1.condition_expr_loc = tok.loc;

      if (!jsp_find_next_token_before_the_locus (TOK_SEMICOLON,
                                                 for_body_statement_loc,
                                                 true))
      {
        EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Invalid for statement");
      }

      current_token_must_be_check_and_skip_it (TOK_SEMICOLON);

      // Save Increment locus
      state_p->u.statement.u.iterational.u.loop_for.u2.increment_expr_loc = tok.loc;

      // Body
      seek_token (for_body_statement_loc);

      JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_STAT_FOR_INCREMENT);
    }
    else if (state_p->state == JSP_STATE_STAT_FOR_INCREMENT)
    {
      if (is_subexpr_end)
      {
        JSP_FINISH_SUBEXPR ();

        state_p->state = JSP_STATE_STAT_FOR_COND;
      }
      else
      {
        // Save LoopEnd locus
        const locus loop_end_loc = tok.loc;

        // Setup ContinueTarget
        JERRY_ASSERT (state_p->u.statement.u.iterational.continue_tgt_oc == MAX_OPCODES);
        state_p->u.statement.u.iterational.continue_tgt_oc = dumper_get_current_instr_counter ();

        // Increment
        seek_token (state_p->u.statement.u.iterational.u.loop_for.u2.increment_expr_loc);

        state_p->u.statement.u.iterational.u.loop_for.u2.end_loc = loop_end_loc;

        if (!token_is (TOK_CLOSE_PAREN))
        {
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);

          jsp_state_top ()->is_need_retval = false;
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
        jsp_operand_t cond = substate_p->u.expression.operand;
        JSP_FINISH_SUBEXPR ();

        dump_continue_iterations_check (state_p->u.statement.u.iterational.u.loop_for.next_iter_tgt_pos, cond);

        state_p->state = JSP_STATE_STAT_FOR_FINISH;
      }
      else
      {
        current_token_must_be (TOK_CLOSE_PAREN);

        // Setup ConditionCheck
        rewrite_jump_to_end (state_p->u.statement.u.iterational.u.loop_for.jump_to_end_pos);

        // Condition
        seek_token (state_p->u.statement.u.iterational.u.loop_for.u1.condition_expr_loc);

        if (token_is (TOK_SEMICOLON))
        {
          dump_continue_iterations_check (state_p->u.statement.u.iterational.u.loop_for.next_iter_tgt_pos, empty_operand ());
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
      seek_token (state_p->u.statement.u.iterational.u.loop_for.u2.end_loc);

      state_p->state = JSP_STATE_STAT_ITER_FINISH;
    }
    else if (state_p->state == JSP_STATE_STAT_FOR_IN)
    {
      current_token_must_be_check_and_skip_it (TOK_CLOSE_PAREN);

      JERRY_ASSERT (is_subexpr_end);

      locus body_loc = tok.loc;

      // Dump for-in instruction
      dump_get_value_if_ref (substate_p, true);

      jsp_operand_t collection = substate_p->u.expression.operand;

      JSP_FINISH_SUBEXPR ();

      state_p->u.statement.u.iterational.u.loop_for_in.header_pos = dump_for_in_for_rewrite (collection);

      // Dump assignment VariableDeclarationNoIn / LeftHandSideExpression <- VM_REG_SPECIAL_FOR_IN_PROPERTY_NAME
      seek_token (state_p->u.statement.u.iterational.u.loop_for_in.u.iterator_expr_loc);

      if (token_is (TOK_KW_VAR))
      {
        skip_token ();

        locus name_loc = tok.loc;

        current_token_must_be (TOK_NAME);

        const lit_cpointer_t lit_cp = token_data_as_lit_cp ();
        const jsp_operand_t name = literal_operand (lit_cp);

        skip_token ();

        jsp_early_error_check_for_eval_and_arguments_in_strict_mode (name, is_strict_mode (), name_loc);

        if (!scopes_tree_variable_declaration_exists (dumper_get_scope (), lit_cp))
        {
          dump_variable_declaration (lit_cp);
        }

        if (token_is (TOK_EQ))
        {
          seek_token (name_loc);

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, false);
        }
        state_p->is_var_decl_no_in = true;
        state_p->u.statement.u.iterational.u.loop_for_in.var_name_lit_cp = lit_cp;
      }
      else
      {
        state_p->is_var_decl_no_in = false;
        state_p->u.statement.u.iterational.u.loop_for_in.var_name_lit_cp = NOT_A_LITERAL;
        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_LEFTHANDSIDE, true);
      }

      // Body
      state_p->u.statement.u.iterational.u.loop_for_in.u.body_loc = body_loc;

      state_p->state = JSP_STATE_STAT_FOR_IN_EXPR;
    }
    else if (state_p->state == JSP_STATE_STAT_FOR_IN_EXPR)
    {
      current_token_must_be (TOK_KW_IN);

      seek_token (state_p->u.statement.u.iterational.u.loop_for_in.u.body_loc);

      jsp_operand_t for_in_special_reg = jsp_operand_t::make_reg_operand (VM_REG_SPECIAL_FOR_IN_PROPERTY_NAME);

      if (!state_p->is_var_decl_no_in)
      {
        JERRY_ASSERT (is_subexpr_end);

        if (substate_p->is_value_based_reference)
        {
          dump_prop_setter (substate_p->u.expression.operand, substate_p->u.expression.prop_name_operand, for_in_special_reg);
        }
        else
        {
          dump_variable_assignment (substate_p->u.expression.operand, for_in_special_reg);
        }

        JSP_FINISH_SUBEXPR ();
      }
      else
      {
        JERRY_ASSERT (!is_subexpr_end);

        lit_cpointer_t var_name_lit_cp = state_p->u.statement.u.iterational.u.loop_for_in.var_name_lit_cp;

        dump_variable_assignment (jsp_operand_t::make_identifier_operand (var_name_lit_cp), for_in_special_reg);
      }

      state_p->is_simply_jumpable_border = true;

      JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_STAT_FOR_IN_FINISH);
    }
    else if (state_p->state == JSP_STATE_STAT_FOR_IN_FINISH)
    {
      // Save LoopEnd locus
      const locus loop_end_loc = tok.loc;

      // Setup ContinueTarget
      JERRY_ASSERT (state_p->u.statement.u.iterational.continue_tgt_oc == MAX_OPCODES);
      state_p->u.statement.u.iterational.continue_tgt_oc = dumper_get_current_instr_counter ();

      // Write position of for-in end to for_in instruction
      rewrite_for_in (state_p->u.statement.u.iterational.u.loop_for_in.header_pos);

      // Dump meta (OPCODE_META_TYPE_END_FOR_IN)
      dump_for_in_end ();

      seek_token (loop_end_loc);

      state_p->state = JSP_STATE_STAT_ITER_FINISH;
    }
    else if (state_p->state == JSP_STATE_STAT_ITER_FINISH)
    {
      JSP_COMPLETE_STATEMENT_PARSE ();

      jsp_rewrite_jumps_chain (&state_p->u.statement.u.iterational.continues_rewrite_chain,
                               state_p->u.statement.u.iterational.continue_tgt_oc);
    }
    else if (state_p->state == JSP_STATE_STAT_SWITCH)
    {
      JERRY_ASSERT (is_subexpr_end);

      parse_expression_inside_parens_end ();

      dump_get_value_if_ref (substate_p, false);

      jsp_operand_t switch_expr = substate_p->u.expression.operand;

      JSP_FINISH_SUBEXPR ();

      current_token_must_be_check_and_skip_it (TOK_OPEN_BRACE);

      state_p->state = JSP_STATE_STAT_SWITCH_BRANCH_EXPR;

      state_p->u.statement.u.switch_statement.expr = switch_expr;
      state_p->u.statement.u.switch_statement.default_label_oc = MAX_OPCODES;
      state_p->u.statement.u.switch_statement.last_cond_check_jmp_oc = MAX_OPCODES;
      state_p->u.statement.u.switch_statement.skip_check_jmp_oc = MAX_OPCODES;

      dumper_save_reg_alloc_ctx (&state_p->u.statement.u.switch_statement.saved_reg_next,
                                 &state_p->u.statement.u.switch_statement.saved_reg_max_for_temps);
    }
    else if (state_p->state == JSP_STATE_STAT_SWITCH_BRANCH_EXPR)
    {
      if (is_subexpr_end)
      {
        /* finished parse of an Expression in CaseClause */
        dump_get_value_if_ref (substate_p, true);

        jsp_operand_t case_expr = substate_p->u.expression.operand;

        JSP_FINISH_SUBEXPR ();

        current_token_must_be_check_and_skip_it (TOK_COLON);

        jsp_operand_t switch_expr = state_p->u.statement.u.switch_statement.expr;

        jsp_operand_t condition_reg;
        if (case_expr.is_register_operand ())
        {
          /* reuse the register */
          condition_reg = case_expr;
        }
        else
        {
          condition_reg = tmp_operand ();
        }

        dump_binary_op (VM_OP_EQUAL_VALUE_TYPE, condition_reg, switch_expr, case_expr);

        jsp_add_conditional_jump_to_rewrite_chain (&state_p->u.statement.u.switch_statement.last_cond_check_jmp_oc,
                                                   true, condition_reg);

        uint32_t num = jsp_rewrite_jumps_chain (&state_p->u.statement.u.switch_statement.skip_check_jmp_oc,
                                                dumper_get_current_instr_counter ());
        JERRY_ASSERT (num <= 1);

        jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT_LIST);
        jsp_state_top ()->req_state = JSP_STATE_STAT_STATEMENT_LIST;
      }
      else if (token_is (TOK_CLOSE_BRACE))
      {
        skip_token ();

        vm_instr_counter_t last_cond_check_tgt_oc;

        if (state_p->u.statement.u.switch_statement.default_label_oc != MAX_OPCODES)
        {
          last_cond_check_tgt_oc = state_p->u.statement.u.switch_statement.default_label_oc;
        }
        else
        {
          last_cond_check_tgt_oc = dumper_get_current_instr_counter ();
        }

        uint32_t num = jsp_rewrite_jumps_chain (&state_p->u.statement.u.switch_statement.last_cond_check_jmp_oc,
                                                last_cond_check_tgt_oc);
        JERRY_ASSERT (num <= 1);

        JSP_COMPLETE_STATEMENT_PARSE ();
      }
      else
      {
        if (is_stmt_list_end
            && !is_stmt_list_control_flow_exit_stmt_occured
            && token_is (TOK_KW_CASE))
        {
          jsp_add_simple_jump_to_rewrite_chain (&state_p->u.statement.u.switch_statement.skip_check_jmp_oc);
        }

        if (token_is (TOK_KW_CASE) || token_is (TOK_KW_DEFAULT))
        {
          uint32_t num = jsp_rewrite_jumps_chain (&state_p->u.statement.u.switch_statement.last_cond_check_jmp_oc,
                                                  dumper_get_current_instr_counter ());
          JERRY_ASSERT (num <= 1);

          if (!is_stmt_list_end /* no StatementList[opt] occured in the SwitchStatement yet,
                                 * so no conditions were checked for now and the DefaultClause
                                 * should be jumped over */
              && token_is (TOK_KW_DEFAULT))
          {
            /* first clause is DefaultClause */
            JERRY_ASSERT (state_p->u.statement.u.switch_statement.default_label_oc == MAX_OPCODES);

            /* the check is unconditional as it is jump over DefaultClause */
            jsp_add_simple_jump_to_rewrite_chain (&state_p->u.statement.u.switch_statement.last_cond_check_jmp_oc);
          }

          if (token_is (TOK_KW_CASE))
          {
            skip_token ();

            dumper_restore_reg_alloc_ctx (state_p->u.statement.u.switch_statement.saved_reg_next,
                                          state_p->u.statement.u.switch_statement.saved_reg_max_for_temps);

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
          }
          else
          {
            JERRY_ASSERT (token_is (TOK_KW_DEFAULT));
            skip_token ();

            if (state_p->u.statement.u.switch_statement.default_label_oc != MAX_OPCODES)
            {
              EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Duplication of 'default' clause");
            }

            state_p->u.statement.u.switch_statement.default_label_oc = dumper_get_current_instr_counter ();

            uint32_t num = jsp_rewrite_jumps_chain (&state_p->u.statement.u.switch_statement.skip_check_jmp_oc,
                                                    dumper_get_current_instr_counter ());
            JERRY_ASSERT (num <= 1);

            current_token_must_be_check_and_skip_it (TOK_COLON);

            jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT_LIST);
            jsp_state_top ()->req_state = JSP_STATE_STAT_STATEMENT_LIST;
          }
        }
        else
        {
          EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Expected 'case' or' 'default' clause");
        }
      }
    }
    else if (state_p->state == JSP_STATE_STAT_TRY)
    {
      rewrite_try (state_p->u.statement.u.try_statement.try_pos);

      if (!token_is (TOK_KW_CATCH)
          && !token_is (TOK_KW_FINALLY))
      {
        EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Expected either 'catch' or 'finally' token");
      }

      if (token_is (TOK_KW_CATCH))
      {
        skip_token ();

        current_token_must_be_check_and_skip_it (TOK_OPEN_PAREN);

        current_token_must_be (TOK_NAME);

        const jsp_operand_t name = literal_operand (token_data_as_lit_cp ());
        jsp_early_error_check_for_eval_and_arguments_in_strict_mode (name, is_strict_mode (), tok.loc);

        skip_token ();

        current_token_must_be_check_and_skip_it (TOK_CLOSE_PAREN);

        state_p->u.statement.u.try_statement.catch_pos = dump_catch_for_rewrite (name);

        current_token_must_be_check_and_skip_it (TOK_OPEN_BRACE);

        state_p->state = JSP_STATE_STAT_CATCH_FINISH;

        JERRY_ASSERT (state_p->is_simply_jumpable_border);

        jsp_start_statement_parse (JSP_STATE_STAT_BLOCK);
        jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT_LIST);
        jsp_state_top ()->req_state = JSP_STATE_STAT_STATEMENT_LIST;
      }
      else
      {
        JERRY_ASSERT (token_is (TOK_KW_FINALLY));
        skip_token ();

        state_p->u.statement.u.try_statement.finally_pos = dump_finally_for_rewrite ();

        current_token_must_be_check_and_skip_it (TOK_OPEN_BRACE);

        state_p->state = JSP_STATE_STAT_FINALLY_FINISH;

        JERRY_ASSERT (state_p->is_simply_jumpable_border);

        jsp_start_statement_parse (JSP_STATE_STAT_BLOCK);
        jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT_LIST);
        jsp_state_top ()->req_state = JSP_STATE_STAT_STATEMENT_LIST;
      }
    }
    else if (state_p->state == JSP_STATE_STAT_CATCH_FINISH)
    {
      rewrite_catch (state_p->u.statement.u.try_statement.catch_pos);

      if (token_is (TOK_KW_FINALLY))
      {
        skip_token ();
        state_p->u.statement.u.try_statement.finally_pos = dump_finally_for_rewrite ();

        current_token_must_be_check_and_skip_it (TOK_OPEN_BRACE);

        state_p->state = JSP_STATE_STAT_FINALLY_FINISH;

        JERRY_ASSERT (state_p->is_simply_jumpable_border);

        jsp_start_statement_parse (JSP_STATE_STAT_BLOCK);
        jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT_LIST);
        jsp_state_top ()->req_state = JSP_STATE_STAT_STATEMENT_LIST;
      }
      else
      {
        state_p->state = JSP_STATE_STAT_TRY_FINISH;
      }
    }
    else if (state_p->state == JSP_STATE_STAT_FINALLY_FINISH)
    {
      rewrite_finally (state_p->u.statement.u.try_statement.finally_pos);

      state_p->state = JSP_STATE_STAT_TRY_FINISH;
    }
    else if (state_p->state == JSP_STATE_STAT_TRY_FINISH)
    {
      dump_end_try_catch_finally ();

      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else if (state_p->state == JSP_STATE_STAT_WITH)
    {
      if (is_subexpr_end)
      {
        parse_expression_inside_parens_end();
        const jsp_operand_t expr = substate_p->u.expression.operand;

        JSP_FINISH_SUBEXPR ();

        scopes_tree_set_contains_with (dumper_get_scope ());

        state_p->is_simply_jumpable_border = true;

        state_p->u.statement.u.with_statement.header_pos = dump_with_for_rewrite (expr);

        JSP_PUSH_STATE_AND_STATEMENT_PARSE (JSP_STATE_STAT_WITH);
      }
      else
      {
        rewrite_with (state_p->u.statement.u.with_statement.header_pos);
        dump_with_end ();

        JSP_COMPLETE_STATEMENT_PARSE ();
      }
    }
    else if (state_p->state == JSP_STATE_FUNC_DECL_FINISH)
    {
      jsp_finish_parse_function_scope (false);
      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else if (state_p->state == JSP_STATE_STAT_NAMED_LABEL)
    {
      jsp_state_pop ();
    }
    else if (state_p->state == JSP_STATE_STAT_EXPRESSION)
    {
      JERRY_ASSERT (is_subexpr_end);
      insert_semicolon ();

      dump_get_value_if_ref (substate_p, false);

      if (dumper_get_scope ()->type == SCOPE_TYPE_EVAL)
      {
        JERRY_ASSERT (substate_p->is_need_retval);

        dump_variable_assignment (jsp_operand_t::make_reg_operand (VM_REG_SPECIAL_EVAL_RET),
                                  substate_p->u.expression.operand);
      }

      JSP_FINISH_SUBEXPR ();

      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else if (state_p->state == JSP_STATE_STAT_RETURN)
    {
      JERRY_ASSERT (is_subexpr_end);

      dump_get_value_if_ref (substate_p, true);

      const jsp_operand_t op = substate_p->u.expression.operand;

      JSP_FINISH_SUBEXPR ();

      dump_retval (op);

      insert_semicolon ();

      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else if (state_p->state == JSP_STATE_STAT_THROW)
    {
      JERRY_ASSERT (is_subexpr_end);

      dump_get_value_if_ref (substate_p, true);

      const jsp_operand_t op = substate_p->u.expression.operand;

      JSP_FINISH_SUBEXPR ();

      dump_throw (op);

      insert_semicolon ();

      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else
    {
      JERRY_ASSERT (state_p->state == JSP_STATE_STAT_STATEMENT);
      JERRY_ASSERT (!state_p->is_completed);

      vm_instr_counter_t break_tgt_oc = dumper_get_current_instr_counter ();
      jsp_rewrite_jumps_chain (&state_p->u.statement.breaks_rewrite_chain,
                               break_tgt_oc);

      state_p->is_completed = true;
    }

    JERRY_ASSERT (substate_p == NULL);
  }
} /* jsp_parse_source_element_list */

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

  jsp_stack_init ();

  dumper_init (parser_show_instrs);
  jsp_early_error_init ();

  scopes_tree scope = scopes_tree_init (NULL, scope_type);
  dumper_set_scope (scope);
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

    skip_token ();

    jsp_parse_directive_prologue ();

    // jsp_parse_source_element_list (PREPARSE);
    jsp_parse_source_element_list (DUMP);

    JERRY_ASSERT (token_is (TOK_EOF));

    if (scope_type == SCOPE_TYPE_EVAL)
    {
      dump_retval (jsp_operand_t::make_reg_operand (VM_REG_SPECIAL_EVAL_RET));
    }
    else
    {
      dump_ret ();
    }

#ifndef JERRY_NDEBUG
    is_parse_finished = true;
#endif /* !JERRY_NDEBUG */

    jsp_early_error_free ();

    *out_bytecode_data_p = bc_merge_scopes_into_bytecode (dumper_get_scope (),
                                                          parser_show_instrs);

    dumper_free ();

    if (out_contains_functions_p != NULL)
    {
      *out_contains_functions_p = scope->contains_functions;
    }

    dumper_set_scope (NULL);
    scopes_tree_free (scope);

    jsp_stack_finalize ();

    status = JSP_STATUS_OK;
  }
  else
  {
    /* SyntaxError handling */

#ifndef JERRY_NDEBUG
    JERRY_ASSERT (!is_parse_finished);
#endif /* !JERRY_NDEBUG */

    *out_bytecode_data_p = NULL;

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
