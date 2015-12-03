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
static bool is_generate_bytecode = true;

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
  JSP_STATE_EXPR_UNARY,               /**< UnaryExpression (11.4) */
  JSP_STATE_EXPR_MULTIPLICATIVE,      /**< MultiplicativeExpression (11.5) */
  JSP_STATE_EXPR_ADDITIVE,            /**< AdditiveExpression (11.6) */
  JSP_STATE_EXPR_SHIFT,               /**< ShiftExpression (11.7) */
  JSP_STATE_EXPR_RELATIONAL,          /**< RelationalExpression (11.8) */
  JSP_STATE_EXPR_EQUALITY,            /**< EqualityExpression (11.9) */
  JSP_STATE_EXPR_BITWISE_AND,         /**< BitwiseAndExpression (11.10) */
  JSP_STATE_EXPR_BITWISE_XOR,         /**< BitwiseXorExpression (11.10) */
  JSP_STATE_EXPR_BITWISE_OR,          /**< BitwiseOrExpression (11.10) */
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

static void jsp_parse_source_element_list ();
static void skip_case_clause_body (void);

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

/*
 * FIXME:
 *       Move the functionality to dumper
 */
static jsp_operand_t
dump_get_value_if_value_based_ref (jsp_operand_t obj,
                                   jsp_operand_t prop_name,
                                   bool is_value_based_reference)
{
  if (is_value_based_reference)
  {
    JERRY_ASSERT (!prop_name.is_empty_operand ());

    jsp_operand_t reg = tmp_operand ();

    dump_prop_getter (reg, obj, prop_name);

    return reg;
  }
  else
  {
    JERRY_ASSERT (prop_name.is_empty_operand ());

    return obj;
  }
}

static jsp_operand_t
dump_get_value_if_ref (jsp_operand_t obj,
                       jsp_operand_t prop_name,
                       bool is_value_based_reference)
{
  if (is_value_based_reference)
  {
    JERRY_ASSERT (!prop_name.is_empty_operand ());

    jsp_operand_t reg = tmp_operand ();

    dump_prop_getter (reg, obj, prop_name);

    return reg;
  }
  else if (obj.is_identifier_operand ())
  {
    jsp_operand_t reg = tmp_operand ();

    dump_variable_assignment (reg, obj);

    return reg;
  }
  else if (obj.is_register_operand ()
           && !(obj.get_idx () >= VM_REG_GENERAL_FIRST && obj.get_idx () <= VM_REG_GENERAL_LAST))
  {
    jsp_operand_t general_reg = tmp_operand ();

    dump_variable_assignment (general_reg, obj);

    return general_reg;
  }
  else
  {
    return obj;
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
  JERRY_ASSERT (dumper_get_scope ()->type == SCOPE_TYPE_FUNCTION);

  vm_instr_counter_t instr_pos = 0u;

  if (is_generate_bytecode)
  {
    const vm_instr_counter_t header_oc = instr_pos++;
    op_meta header_opm = dumper_get_op_meta (header_oc);
    JERRY_ASSERT (header_opm.op.op_idx == VM_OP_FUNC_EXPR_N || header_opm.op.op_idx == VM_OP_FUNC_DECL_N);

    while (true)
    {
      op_meta meta_opm = dumper_get_op_meta (instr_pos);
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
  uint8_t is_value_based_reference  : 1; /**< flag, indicating whether current state represents evaluated expression
                                          *   that evaluated to a value-based reference */
  uint8_t is_complex_production     : 1; /**< the expression is being parsed in complex production mode */
  uint8_t var_decl                  : 1; /**< this flag tells that we are parsing VariableStatement, not
                                            VariableDeclarationList or VariableDeclaration inside
                                            IterationStatement */
  uint8_t is_var_decl_no_in       : 1; /**< this flag tells that we are parsing VariableDeclrationNoIn inside
                                            ForIn iteration statement */
  uint8_t was_default             : 1; /**< was default branch seen */
  uint8_t is_default_branch         : 1; /**< marks default branch of switch statement */
  uint8_t is_simply_jumpable_border : 1; /**< flag, indicating whether simple jump could be performed
                                          *   from current statement outside of the statement */
  uint8_t is_dump_eval_ret_store  : 1; /**< expression's result should be stored to eval's return register */

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
          locus loc;
          jsp_operand_t expr;

          vm_instr_counter_t jmp_oc;

          uint16_t case_clause_count;
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
jsp_state_t jsp_state_stack[JSP_STATE_STACK_MAX];
uint32_t jsp_state_stack_pos;

static void
jsp_stack_init (void)
{
  jsp_state_stack_pos = 0;
} /* jsp_stack_init */

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

  new_state.is_no_in_mode = !in_allowed;

  jsp_state_push (new_state);
} /* jsp_push_new_expr_state */

/*
 * FIXME:
 *       Move to dumper
 */
static vm_instr_counter_t
jsp_start_call_dump (jsp_operand_t obj,
                     jsp_operand_t prop_name,
                     bool is_value_based_reference)
{
  opcode_call_flags_t call_flags = OPCODE_CALL_FLAGS__EMPTY;

  jsp_operand_t val;

  if (is_value_based_reference)
  {
    if (obj.is_identifier_operand ())
    {
      obj = dump_get_value_if_ref (obj, empty_operand (), false);
    }

    val = tmp_operand ();
    dump_prop_getter (val, obj, prop_name);

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

    val = obj;
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
    val = obj;
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
  jsp_operand_t ret = tmp_operand ();

  rewrite_varg_header_set_args_count (ret, args_num, header_pos);

  return ret;
} /* jsp_finish_call_dump */

/*
 * FIXME:
 *       Move to dumper
 */
static vm_instr_counter_t __attr_unused___
jsp_start_construct_dump (jsp_operand_t obj,
                          jsp_operand_t prop_name,
                          bool is_value_based_reference)
{
  return dump_varg_header_for_rewrite (VARG_CONSTRUCT_EXPR,
                                       dump_get_value_if_value_based_ref (obj,
                                                                          prop_name,
                                                                          is_value_based_reference));
} /* jsp_start_construct_dump */

/*
 * FIXME:
 *       Move to dumper
 */
static jsp_operand_t __attr_unused___
jsp_finish_construct_dump (uint32_t args_num,
                           vm_instr_counter_t header_pos)
{
  jsp_operand_t ret = tmp_operand ();

  rewrite_varg_header_set_args_count (ret, args_num, header_pos);

  return ret;
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
    jsp_state_t *state_p = &jsp_state_stack [--stack_pos];

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
    bool is_switch_stmt = (state_p->state == JSP_STATE_STAT_SWITCH_FINISH);

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
    jsp_state_t *state_p = &jsp_state_stack [--stack_pos];

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
        state_p = &jsp_state_stack [stack_pos];

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

/**
 * Parse source element list
 */
static void __attr_noinline___
jsp_parse_source_element_list ()
{
  jsp_stack_init ();

  jsp_start_statement_parse (JSP_STATE_SOURCE_ELEMENTS_INIT);
  jsp_state_top ()->req_state = JSP_STATE_SOURCE_ELEMENTS;

  while (true)
  {
    bool is_source_elements_list_end = false;
    bool is_subexpr_end = false, is_subexpr_value_based_reference = false;
    jsp_operand_t subexpr_operand, subexpr_prop_name_operand = empty_operand ();
    jsp_state_expr_t subexpr_type;

    jsp_state_t *state_p = jsp_state_top ();

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
        JERRY_STATIC_ASSERT (JSP_STATE_EXPR__BEGIN == 0);
        is_subexpr_end = (state_p->state <= JSP_STATE_EXPR__END);

        if (is_subexpr_end)
        {
          subexpr_operand = state_p->u.expression.operand;
          subexpr_type = state_p->state;

          if (state_p->is_value_based_reference)
          {
            is_subexpr_value_based_reference = true;
            subexpr_prop_name_operand = state_p->u.expression.prop_name_operand;

            JERRY_ASSERT (!subexpr_prop_name_operand.is_empty_operand ());
          }
        }
        else if (state_p->req_state == JSP_STATE_SOURCE_ELEMENTS)
        {
          is_source_elements_list_end = true;
        }

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
      JERRY_ASSERT (!(state_p->state == JSP_STATE_EXPR_EXPRESSION && state_p->req_state != JSP_STATE_EXPR_EXPRESSION));
    }

    const bool in_allowed = !state_p->is_no_in_mode;

    if (state_p->state == JSP_STATE_SOURCE_ELEMENTS_INIT)
    {
      scope_type_t scope_type = dumper_get_scope ()->type;

      dumper_new_scope (&state_p->u.source_elements.saved_reg_next,
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
        if (is_generate_bytecode)
        {
          scope_flags = jsp_try_move_vars_to_regs (state_p, scope_flags);
        }
#endif /* CONFIG_PARSER_ENABLE_PARSE_TIME_BYTE_CODE_OPTIMIZER */

        rewrite_scope_code_flags (state_p->u.source_elements.scope_code_flags_oc, scope_flags);
        rewrite_reg_var_decl (state_p->u.source_elements.reg_var_decl_oc);

        state_p->is_completed = true;

        dumper_finish_scope (state_p->u.source_elements.saved_reg_next,
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
        /* ArrayLiteral */
        vm_instr_counter_t varg_header_pos = dump_varg_header_for_rewrite (VARG_ARRAY_DECL, empty_operand ());

        state_p->state = JSP_STATE_EXPR_ARRAY_LITERAL;
        state_p->is_list_in_process = true;
        state_p->u.expression.u.varg_sequence.list_length = 0;
        state_p->u.expression.u.varg_sequence.header_pos = varg_header_pos;
      }
      else if (token_is (TOK_OPEN_BRACE))
      {
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
            break;
          }
          case TOK_KW_THIS:
          {
            state_p->u.expression.operand = jsp_operand_t::make_reg_operand (VM_REG_SPECIAL_THIS_BINDING);
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
        JERRY_ASSERT (subexpr_type == JSP_STATE_EXPR_ASSIGNMENT);

        jsp_operand_t prop_name = state_p->u.expression.operand;
        jsp_operand_t value = dump_get_value_if_value_based_ref (subexpr_operand,
                                                                 subexpr_prop_name_operand,
                                                                 is_subexpr_value_based_reference);

        JERRY_ASSERT (prop_name.is_literal_operand ());

        dump_prop_name_and_value (prop_name, value);
        jsp_early_error_add_prop_name (prop_name, PROP_DATA);

        state_p->is_completed = true;
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
        JERRY_ASSERT (subexpr_type == JSP_STATE_EXPR_DATA_PROP_DECL
                      || subexpr_type == JSP_STATE_EXPR_ACCESSOR_PROP_DECL);

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
        subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                             subexpr_prop_name_operand,
                                                             is_subexpr_value_based_reference);

        dump_varg (subexpr_operand);

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
            JERRY_ASSERT (subexpr_type == JSP_STATE_EXPR_ASSIGNMENT);

            subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                                 subexpr_prop_name_operand,
                                                                 is_subexpr_value_based_reference);
            dump_varg (subexpr_operand);

            dumper_finish_varg_code_sequence (state_p->u.expression.u.varg_sequence.reg_alloc_saved_state);

            state_p->u.expression.u.varg_sequence.list_length++;

            if (token_is (TOK_CLOSE_PAREN))
            {
              state_p->u.expression.token_type = TOK_EMPTY;
              state_p->is_list_in_process = false;

              uint32_t list_len = state_p->u.expression.u.varg_sequence.list_length;
              vm_instr_counter_t header_pos = state_p->u.expression.u.varg_sequence.header_pos;

              state_p->u.expression.operand = jsp_finish_construct_dump (list_len, header_pos);
              state_p->u.expression.prop_name_operand = empty_operand ();
              state_p->is_value_based_reference = false;
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

            state_p->u.expression.operand = subexpr_operand;
            state_p->u.expression.prop_name_operand = subexpr_prop_name_operand;
            state_p->is_value_based_reference = is_subexpr_value_based_reference;

            state_p->u.expression.token_type = TOK_EMPTY;

            current_token_must_be_check_and_skip_it (TOK_CLOSE_PAREN);
          }
          else if (state_p->u.expression.token_type == TOK_KW_NEW)
          {
            JERRY_ASSERT (subexpr_type == JSP_STATE_EXPR_MEMBER);
            JERRY_ASSERT (state_p->u.expression.operand.is_empty_operand ());
            JERRY_ASSERT (!subexpr_operand.is_empty_operand ());

            state_p->u.expression.operand = subexpr_operand;
            state_p->u.expression.prop_name_operand = subexpr_prop_name_operand;
            state_p->is_value_based_reference = is_subexpr_value_based_reference;

            vm_instr_counter_t header_pos = jsp_start_construct_dump (state_p->u.expression.operand,
                                                                      state_p->u.expression.prop_name_operand,
                                                                      state_p->is_value_based_reference);

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
              state_p->u.expression.u.varg_sequence.list_length = 0;
              state_p->u.expression.u.varg_sequence.header_pos = header_pos;
              state_p->u.expression.u.varg_sequence.reg_alloc_saved_state = dumper_start_varg_code_sequence ();

              jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);
            }
            else
            {
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

            /*
             * FIXME:
             *       evaluation order - change to dump_get_value_if_ref
             */
            subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                                 subexpr_prop_name_operand,
                                                                 is_subexpr_value_based_reference);

            state_p->u.expression.prop_name_operand = subexpr_operand;
            state_p->is_value_based_reference = true;
          }
        }
        else if (token_is (TOK_OPEN_SQUARE))
        {
          skip_token ();

          state_p->u.expression.token_type = TOK_OPEN_SQUARE;

          jsp_operand_t base = dump_get_value_if_value_based_ref (state_p->u.expression.operand,
                                                                  state_p->u.expression.prop_name_operand,
                                                                  state_p->is_value_based_reference);
          state_p->u.expression.operand = base;
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
        }
        else if (token_is (TOK_DOT))
        {
          skip_token ();

          lit_cpointer_t prop_name = jsp_get_prop_name_after_dot ();
          skip_token ();

          jsp_operand_t base = dump_get_value_if_value_based_ref (state_p->u.expression.operand,
                                                                  state_p->u.expression.prop_name_operand,
                                                                  state_p->is_value_based_reference);

          state_p->u.expression.operand = base;

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
          JERRY_ASSERT (subexpr_type == JSP_STATE_EXPR_ASSIGNMENT);

          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);
          dump_varg (subexpr_operand);

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

          /*
           * FIXME:
           *       evaluation order - change to dump_get_value_if_ref
           */
          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);
          state_p->u.expression.prop_name_operand = subexpr_operand;
          state_p->is_value_based_reference = true;
        }

        skip_token ();
      }
      else
      {
        if (token_is (TOK_OPEN_PAREN))
        {
          skip_token ();

          vm_instr_counter_t header_pos = jsp_start_call_dump (state_p->u.expression.operand,
                                                               state_p->u.expression.prop_name_operand,
                                                               state_p->is_value_based_reference);

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
          state_p->u.expression.operand = dump_get_value_if_ref (state_p->u.expression.operand,
                                                                 state_p->u.expression.prop_name_operand,
                                                                 state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
        }
        else if (token_is (TOK_DOT))
        {
          skip_token ();

          lit_cpointer_t prop_name = jsp_get_prop_name_after_dot ();
          skip_token ();

          jsp_operand_t base = dump_get_value_if_ref (state_p->u.expression.operand,
                                                      state_p->u.expression.prop_name_operand,
                                                      state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;

          state_p->u.expression.operand = base;

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

        state_p->state = JSP_STATE_EXPR_ASSIGNMENT;
        state_p->u.expression.token_type = TOK_EMPTY;
        state_p->is_completed = true;

        JERRY_ASSERT (tt >= TOKEN_TYPE__ASSIGNMENTS_BEGIN && tt <= TOKEN_TYPE__ASSIGNMENTS_END);

        subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                             subexpr_prop_name_operand,
                                                             is_subexpr_value_based_reference);

        if (tt == TOK_EQ)
        {
          if (state_p->is_value_based_reference)
          {
            dump_prop_setter (state_p->u.expression.operand,
                              state_p->u.expression.prop_name_operand,
                              subexpr_operand);
          }
          else
          {
            dump_variable_assignment (state_p->u.expression.operand, subexpr_operand);
          }

          state_p->u.expression.operand = subexpr_operand;
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;
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

            dump_binary_op (opcode, reg, reg, subexpr_operand);

            dump_prop_setter (state_p->u.expression.operand,
                              state_p->u.expression.prop_name_operand,
                              reg);

            state_p->u.expression.operand = reg;
            state_p->u.expression.prop_name_operand = empty_operand ();
            state_p->is_value_based_reference = false;
          }
          else
          {
            dump_binary_op (opcode, state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }
        }
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

        if (state_p->u.expression.token_type == TOK_DOUBLE_PLUS)
        {
          jsp_operand_t reg = tmp_operand ();

          if (is_subexpr_value_based_reference)
          {
            dump_prop_getter (reg, subexpr_operand, subexpr_prop_name_operand);

            dump_unary_op (VM_OP_PRE_INCR, reg, reg);

            dump_prop_setter (subexpr_operand, subexpr_prop_name_operand, reg);
          }
          else if (subexpr_operand.is_identifier_operand ())
          {
            jsp_early_error_check_for_eval_and_arguments_in_strict_mode (subexpr_operand, is_strict_mode (), tok.loc);

            dump_unary_op (VM_OP_PRE_INCR, reg, subexpr_operand);
          }
          else
          {
            PARSE_ERROR (JSP_EARLY_ERROR_REFERENCE, "Invalid left-hand-side expression", tok.loc);
          }

          state_p->u.expression.operand = reg;
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;
        }
        else if (state_p->u.expression.token_type == TOK_DOUBLE_MINUS)
        {
          jsp_operand_t reg = tmp_operand ();

          if (is_subexpr_value_based_reference)
          {
            dump_prop_getter (reg, subexpr_operand, subexpr_prop_name_operand);

            dump_unary_op (VM_OP_PRE_DECR, reg, reg);

            dump_prop_setter (subexpr_operand, subexpr_prop_name_operand, reg);
          }
          else if (subexpr_operand.is_identifier_operand ())
          {
            jsp_early_error_check_for_eval_and_arguments_in_strict_mode (subexpr_operand, is_strict_mode (), tok.loc);

            dump_unary_op (VM_OP_PRE_DECR, reg, subexpr_operand);
          }
          else
          {
            PARSE_ERROR (JSP_EARLY_ERROR_REFERENCE, "Invalid left-hand-side expression", tok.loc);
          }

          state_p->u.expression.operand = reg;
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;
        }
        else if (state_p->u.expression.token_type == TOK_PLUS)
        {
          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);

          state_p->u.expression.operand = tmp_operand ();
          dump_unary_plus (state_p->u.expression.operand, subexpr_operand);
        }
        else if (state_p->u.expression.token_type == TOK_MINUS)
        {
          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);

          state_p->u.expression.operand = tmp_operand ();
          dump_unary_minus (state_p->u.expression.operand, subexpr_operand);
        }
        else if (state_p->u.expression.token_type == TOK_COMPL)
        {
          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);

          state_p->u.expression.operand = tmp_operand ();
          dump_bitwise_not (state_p->u.expression.operand, subexpr_operand);
        }
        else if (state_p->u.expression.token_type == TOK_NOT)
        {
          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);

          state_p->u.expression.operand = tmp_operand ();
          dump_logical_not (state_p->u.expression.operand, subexpr_operand);
        }
        else if (state_p->u.expression.token_type == TOK_KW_DELETE)
        {
          state_p->u.expression.operand = tmp_operand ();

          if (!is_subexpr_value_based_reference)
          {
            if (subexpr_operand.is_identifier_operand ())
            {
              jsp_early_error_check_delete (is_strict_mode (), tok.loc);
            }

            dump_delete (state_p->u.expression.operand, subexpr_operand);
          }
          else
          {
            if (subexpr_operand.is_literal_operand ())
            {
              jsp_operand_t reg = tmp_operand ();

              dump_string_assignment (reg, subexpr_operand.get_literal ());

              subexpr_operand = reg;
            }

            dump_delete_prop (state_p->u.expression.operand,
                              subexpr_operand,
                              subexpr_prop_name_operand);
          }
        }
        else if (state_p->u.expression.token_type == TOK_KW_VOID)
        {
          const jsp_operand_t reg = tmp_operand ();

          if (is_subexpr_value_based_reference)
          {
            dump_prop_getter (reg, subexpr_operand, subexpr_prop_name_operand);
          }
          else if (subexpr_operand.is_identifier_operand ())
          {
            dump_variable_assignment (reg, subexpr_operand);
          }

          dump_undefined_assignment (reg);
          state_p->u.expression.operand = reg;
        }
        else
        {
          JERRY_ASSERT (state_p->u.expression.token_type == TOK_KW_TYPEOF);

          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);

          state_p->u.expression.operand = tmp_operand ();
          dump_typeof (state_p->u.expression.operand, subexpr_operand);
        }

        state_p->u.expression.token_type = TOK_EMPTY;
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
          state_p->u.expression.operand = dump_get_value_if_value_based_ref (state_p->u.expression.operand,
                                                                             state_p->u.expression.prop_name_operand,
                                                                             state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;

          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);

          if (state_p->u.expression.token_type == TOK_MULT)
          {
            dump_multiplication (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }
          else if (state_p->u.expression.token_type == TOK_DIV)
          {
            dump_division (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }
          else
          {
            JERRY_ASSERT (state_p->u.expression.token_type == TOK_MOD);

            dump_remainder (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }

          state_p->u.expression.token_type = TOK_EMPTY;
        }
        else if (lexer_get_token_type (tok) >= TOKEN_TYPE__MULTIPLICATIVE_BEGIN
                 && lexer_get_token_type (tok) <= TOKEN_TYPE__MULTIPLICATIVE_END)
        {
          state_p->u.expression.operand = dump_get_value_if_ref (state_p->u.expression.operand,
                                                                 state_p->u.expression.prop_name_operand,
                                                                 state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;

          state_p->u.expression.token_type = lexer_get_token_type (tok);

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
          state_p->u.expression.operand = dump_get_value_if_value_based_ref (state_p->u.expression.operand,
                                                                             state_p->u.expression.prop_name_operand,
                                                                             state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;
          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);

          if (state_p->u.expression.token_type == TOK_PLUS)
          {
            dump_addition (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }
          else
          {
            JERRY_ASSERT (state_p->u.expression.token_type == TOK_MINUS);

            dump_substraction (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }

          state_p->u.expression.token_type = TOK_EMPTY;
        }
        else if (lexer_get_token_type (tok) >= TOKEN_TYPE__ADDITIVE_BEGIN
                 && lexer_get_token_type (tok) <= TOKEN_TYPE__ADDITIVE_END)
        {
          state_p->u.expression.operand = dump_get_value_if_ref (state_p->u.expression.operand,
                                                                 state_p->u.expression.prop_name_operand,
                                                                 state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;

          state_p->u.expression.token_type = lexer_get_token_type (tok);

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
          state_p->u.expression.operand = dump_get_value_if_value_based_ref (state_p->u.expression.operand,
                                                                             state_p->u.expression.prop_name_operand,
                                                                             state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;
          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);

          if (state_p->u.expression.token_type == TOK_LSHIFT)
          {
            dump_left_shift (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }
          else if (state_p->u.expression.token_type == TOK_RSHIFT)
          {
            dump_right_shift (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }
          else
          {
            JERRY_ASSERT (state_p->u.expression.token_type == TOK_RSHIFT_EX);

            dump_right_shift_ex (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }

          state_p->u.expression.token_type = TOK_EMPTY;
        }
        else if (lexer_get_token_type (tok) >= TOKEN_TYPE__SHIFT_BEGIN
                 && lexer_get_token_type (tok) <= TOKEN_TYPE__SHIFT_END)
        {
          state_p->u.expression.operand = dump_get_value_if_ref (state_p->u.expression.operand,
                                                                 state_p->u.expression.prop_name_operand,
                                                                 state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;

          state_p->u.expression.token_type = lexer_get_token_type (tok);

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
          state_p->u.expression.operand = dump_get_value_if_value_based_ref (state_p->u.expression.operand,
                                                                             state_p->u.expression.prop_name_operand,
                                                                             state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;
          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);

          if (state_p->u.expression.token_type == TOK_LESS)
          {
            dump_less_than (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }
          else if (state_p->u.expression.token_type == TOK_GREATER)
          {
            dump_greater_than (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }
          else if (state_p->u.expression.token_type == TOK_LESS_EQ)
          {
            dump_less_or_equal_than (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }
          else if (state_p->u.expression.token_type == TOK_GREATER_EQ)
          {
            dump_greater_or_equal_than (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }
          else if (state_p->u.expression.token_type == TOK_KW_INSTANCEOF)
          {
            dump_instanceof (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }
          else
          {
            JERRY_ASSERT (state_p->u.expression.token_type == TOK_KW_IN);
            JERRY_ASSERT (in_allowed);

            dump_in (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }

          state_p->u.expression.token_type = TOK_EMPTY;
        }
        else if ((lexer_get_token_type (tok) >= TOKEN_TYPE__RELATIONAL_BEGIN
                  && lexer_get_token_type (tok) <= TOKEN_TYPE__RELATIONAL_END)
                 || lexer_get_token_type (tok) == TOK_KW_INSTANCEOF
                 || (in_allowed && lexer_get_token_type (tok) == TOK_KW_IN))
        {
          state_p->u.expression.operand = dump_get_value_if_ref (state_p->u.expression.operand,
                                                                 state_p->u.expression.prop_name_operand,
                                                                 state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;

          state_p->u.expression.token_type = lexer_get_token_type (tok);

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
          state_p->u.expression.operand = dump_get_value_if_value_based_ref (state_p->u.expression.operand,
                                                                             state_p->u.expression.prop_name_operand,
                                                                             state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;
          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);

          if (state_p->u.expression.token_type == TOK_DOUBLE_EQ)
          {
            dump_equal_value (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }
          else if (state_p->u.expression.token_type == TOK_NOT_EQ)
          {
            dump_not_equal_value (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }
          else if (state_p->u.expression.token_type == TOK_TRIPLE_EQ)
          {
            dump_equal_value_type (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }
          else
          {
            JERRY_ASSERT (state_p->u.expression.token_type == TOK_NOT_DOUBLE_EQ);

            dump_not_equal_value_type (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
          }

          state_p->u.expression.token_type = TOK_EMPTY;
        }
        else if (lexer_get_token_type (tok) >= TOKEN_TYPE__EQUALITY_BEGIN
                 && lexer_get_token_type (tok) <= TOKEN_TYPE__EQUALITY_END)
        {
          state_p->u.expression.operand = dump_get_value_if_ref (state_p->u.expression.operand,
                                                                 state_p->u.expression.prop_name_operand,
                                                                 state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;

          state_p->u.expression.token_type = lexer_get_token_type (tok);

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
          state_p->u.expression.operand = dump_get_value_if_value_based_ref (state_p->u.expression.operand,
                                                                             state_p->u.expression.prop_name_operand,
                                                                             state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;
          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);

          JERRY_ASSERT (state_p->u.expression.token_type == TOK_AND);

          state_p->u.expression.token_type = TOK_EMPTY;
          dump_bitwise_and (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
        }
        else if (token_is (TOK_AND))
        {
          skip_token ();

          state_p->u.expression.operand = dump_get_value_if_ref (state_p->u.expression.operand,
                                                                 state_p->u.expression.prop_name_operand,
                                                                 state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;

          state_p->u.expression.token_type = TOK_AND;

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
          state_p->u.expression.operand = dump_get_value_if_value_based_ref (state_p->u.expression.operand,
                                                                             state_p->u.expression.prop_name_operand,
                                                                             state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;
          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);

          JERRY_ASSERT (state_p->u.expression.token_type == TOK_XOR);

          state_p->u.expression.token_type = TOK_EMPTY;
          dump_bitwise_xor (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
        }
        else if (token_is (TOK_XOR))
        {
          skip_token ();

          state_p->u.expression.operand = dump_get_value_if_ref (state_p->u.expression.operand,
                                                                 state_p->u.expression.prop_name_operand,
                                                                 state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;

          state_p->u.expression.token_type = TOK_XOR;

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

        state_p->u.expression.u.logical_and.rewrite_chain = MAX_OPCODES;

        state_p->is_completed = false;
      }
      else
      {
        if (is_subexpr_end)
        {
          state_p->u.expression.operand = dump_get_value_if_value_based_ref (state_p->u.expression.operand,
                                                                             state_p->u.expression.prop_name_operand,
                                                                             state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;
          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);

          JERRY_ASSERT (state_p->u.expression.token_type == TOK_OR);

          state_p->u.expression.token_type = TOK_EMPTY;
          dump_bitwise_or (state_p->u.expression.operand, state_p->u.expression.operand, subexpr_operand);
        }
        else if (token_is (TOK_OR))
        {
          skip_token ();

          state_p->u.expression.operand = dump_get_value_if_ref (state_p->u.expression.operand,
                                                                 state_p->u.expression.prop_name_operand,
                                                                 state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;

          state_p->u.expression.token_type = TOK_OR;

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

        state_p->u.expression.u.logical_or.rewrite_chain = MAX_OPCODES;

        state_p->is_completed = false;
      }
      else
      {
        if (is_subexpr_end)
        {
          state_p->u.expression.operand = dump_get_value_if_value_based_ref (state_p->u.expression.operand,
                                                                             state_p->u.expression.prop_name_operand,
                                                                             state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;
          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);

          JERRY_ASSERT (state_p->u.expression.token_type == TOK_DOUBLE_AND);

          JERRY_ASSERT (state_p->u.expression.operand.is_register_operand ());

          dump_variable_assignment (state_p->u.expression.operand, subexpr_operand);

          state_p->u.expression.token_type = TOK_EMPTY;
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

              state_p->u.expression.operand = dump_get_value_if_value_based_ref (state_p->u.expression.operand,
                                                                                 state_p->u.expression.prop_name_operand,
                                                                                 state_p->is_value_based_reference);
              state_p->u.expression.prop_name_operand = empty_operand ();
              state_p->is_value_based_reference = false;

              dump_variable_assignment (ret, state_p->u.expression.operand);

              state_p->is_fixed_ret_operand = true;
              state_p->u.expression.operand = ret;
            }

            JERRY_ASSERT (state_p->is_complex_production);

            vm_instr_counter_t *rewrite_chain_p = &state_p->u.expression.u.logical_and.rewrite_chain;
            *rewrite_chain_p = dump_simple_or_nested_jump_for_rewrite (VM_OP_IS_FALSE_JMP_DOWN,
                                                                       state_p->u.expression.operand,
                                                                       *rewrite_chain_p);

            state_p->u.expression.token_type = TOK_DOUBLE_AND;

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_BITWISE_OR, in_allowed);
          }
          else
          {
            /* end of LogicalAndExpression */
            JERRY_ASSERT (state_p->u.expression.token_type == TOK_EMPTY);

            vm_instr_counter_t target_oc = dumper_get_current_instr_counter ();

            if (is_generate_bytecode)
            {
              vm_instr_counter_t *rewrite_chain_p = &state_p->u.expression.u.logical_and.rewrite_chain;
              while (*rewrite_chain_p != MAX_OPCODES)
              {
                *rewrite_chain_p = rewrite_simple_or_nested_jump_and_get_next (*rewrite_chain_p,
                                                                               target_oc);
              }
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

          vm_instr_counter_t conditional_check_pos = dump_conditional_check_for_rewrite (state_p->u.expression.operand);
          state_p->u.expression.u.conditional.conditional_check_pos = conditional_check_pos;

          state_p->u.expression.token_type = TOK_QUERY;

          JERRY_ASSERT (!state_p->is_fixed_ret_operand);

          state_p->is_fixed_ret_operand = true;
          state_p->u.expression.operand = tmp_operand ();

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
          subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                               subexpr_prop_name_operand,
                                                               is_subexpr_value_based_reference);

          JERRY_ASSERT (state_p->u.expression.token_type == TOK_DOUBLE_OR);

          JERRY_ASSERT (state_p->u.expression.operand.is_register_operand ());
          dump_variable_assignment (state_p->u.expression.operand, subexpr_operand);

          state_p->u.expression.token_type = TOK_EMPTY;
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

              jsp_operand_t ret = tmp_operand ();

              state_p->u.expression.operand = dump_get_value_if_value_based_ref (state_p->u.expression.operand,
                                                                                 state_p->u.expression.prop_name_operand,
                                                                                 state_p->is_value_based_reference);
              state_p->u.expression.prop_name_operand = empty_operand ();
              state_p->is_value_based_reference = false;

              dump_variable_assignment (ret, state_p->u.expression.operand);

              JERRY_ASSERT (!state_p->is_fixed_ret_operand);
              state_p->is_fixed_ret_operand = true;

              state_p->u.expression.operand = ret;
            }

            JERRY_ASSERT (state_p->is_complex_production);

            vm_instr_counter_t *rewrite_chain_p = &state_p->u.expression.u.logical_or.rewrite_chain;
            *rewrite_chain_p = dump_simple_or_nested_jump_for_rewrite (VM_OP_IS_TRUE_JMP_DOWN,
                                                                       state_p->u.expression.operand,
                                                                       *rewrite_chain_p);

            state_p->u.expression.token_type = TOK_DOUBLE_OR;

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_LOGICAL_AND, in_allowed);
          }
          else
          {
            /* end of LogicalOrExpression */
            JERRY_ASSERT (state_p->u.expression.token_type == TOK_EMPTY);

            vm_instr_counter_t target_oc = dumper_get_current_instr_counter ();

            if (is_generate_bytecode)
            {
              vm_instr_counter_t *rewrite_chain_p = &state_p->u.expression.u.logical_or.rewrite_chain;
              while (*rewrite_chain_p != MAX_OPCODES)
              {
                *rewrite_chain_p = rewrite_simple_or_nested_jump_and_get_next (*rewrite_chain_p,
                                                                               target_oc);
              }
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
        JERRY_ASSERT (subexpr_type == JSP_STATE_EXPR_ASSIGNMENT);

        subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                             subexpr_prop_name_operand,
                                                             is_subexpr_value_based_reference);

        dump_variable_assignment (state_p->u.expression.operand, subexpr_operand);

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
        JERRY_ASSERT (subexpr_type == JSP_STATE_EXPR_ASSIGNMENT);

        subexpr_operand = dump_get_value_if_value_based_ref (subexpr_operand,
                                                             subexpr_prop_name_operand,
                                                             is_subexpr_value_based_reference);

        dump_variable_assignment (state_p->u.expression.operand, subexpr_operand);
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
        JERRY_ASSERT (state_p->u.expression.operand.is_register_operand ());

        if (!subexpr_operand.is_register_operand ())
        {
          /* evaluating, if reference */
          subexpr_operand = dump_get_value_if_ref (subexpr_operand,
                                                   subexpr_prop_name_operand,
                                                   is_subexpr_value_based_reference);
        }

        state_p->u.expression.operand = subexpr_operand;
        state_p->u.expression.prop_name_operand = empty_operand ();
        state_p->is_value_based_reference = false;
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
          state_p->u.expression.operand = dump_get_value_if_ref (state_p->u.expression.operand,
                                                                 state_p->u.expression.prop_name_operand,
                                                                 state_p->is_value_based_reference);
          state_p->u.expression.prop_name_operand = empty_operand ();
          state_p->is_value_based_reference = false;

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
      else if (token_is (TOK_NAME))  // LabelledStatement or ExpressionStatement
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
        }
        else
        {
          seek_token (temp.loc);

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);

          state_p->state = JSP_STATE_STAT_EXPRESSION;
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

        vm_op_t jmp_opcode = is_simply_jumpable ? VM_OP_JMP_DOWN : VM_OP_JMP_BREAK_CONTINUE;
        *rewrite_chain_p = dump_simple_or_nested_jump_for_rewrite (jmp_opcode, empty_operand (), *rewrite_chain_p);

        JSP_COMPLETE_STATEMENT_PARSE ();
      }
      else if (token_is (TOK_KW_RETURN))
      {
        if (dumper_get_scope ()->type != SCOPE_TYPE_FUNCTION)
        {
          EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Return is illegal");
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
        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);

        state_p->state = JSP_STATE_STAT_EXPRESSION;
      }
    }
    else if (state_p->state == JSP_STATE_STAT_BLOCK)
    {
      current_token_must_be_check_and_skip_it (TOK_CLOSE_BRACE);

      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else if (state_p->state == JSP_STATE_STAT_IF_BRANCH_START)
    {
      if (is_subexpr_end) // Finished parsing condition
      {
        parse_expression_inside_parens_end ();

        jsp_operand_t cond = dump_get_value_if_value_based_ref (subexpr_operand,
                                                                subexpr_prop_name_operand,
                                                                is_subexpr_value_based_reference);
        state_p->u.statement.u.if_statement.conditional_check_pos = dump_conditional_check_for_rewrite (cond);

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
      }

      state_p->state = JSP_STATE_STAT_VAR_DECL_FINISH;
    }
    else if (state_p->state == JSP_STATE_STAT_VAR_DECL_FINISH)
    {
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

        const jsp_operand_t cond = subexpr_operand;
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

        const jsp_operand_t cond = subexpr_operand;
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

      locus body_loc = tok.loc;

      // Dump for-in instruction
      jsp_operand_t collection = dump_get_value_if_value_based_ref (subexpr_operand,
                                                                    subexpr_prop_name_operand,
                                                                    is_subexpr_value_based_reference);
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

        if (is_subexpr_value_based_reference)
        {
          dump_prop_setter (subexpr_operand, subexpr_prop_name_operand, for_in_special_reg);
        }
        else
        {
          dump_variable_assignment (subexpr_operand, for_in_special_reg);
        }
      }
      else
      {
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

      vm_instr_counter_t *rewrite_chain_p = &state_p->u.statement.u.iterational.continues_rewrite_chain;
      vm_instr_counter_t continue_tgt_oc = state_p->u.statement.u.iterational.continue_tgt_oc;

      if (is_generate_bytecode)
      {
        while (*rewrite_chain_p != MAX_OPCODES)
        {
          *rewrite_chain_p = rewrite_simple_or_nested_jump_and_get_next (*rewrite_chain_p,
                                                                         continue_tgt_oc);
        }
      }
    }
    else if (state_p->state == JSP_STATE_STAT_SWITCH)
    {
      JERRY_ASSERT (is_subexpr_end);

      parse_expression_inside_parens_end ();
      jsp_operand_t switch_expr = dump_get_value_if_ref (subexpr_operand,
                                                         subexpr_prop_name_operand,
                                                         is_subexpr_value_based_reference);

      locus start_loc = tok.loc;

      current_token_must_be_check_and_skip_it (TOK_OPEN_BRACE);

      // First, generate table of jumps
      start_dumping_case_clauses ();

      state_p->state = JSP_STATE_STAT_SWITCH_FINISH;
      jsp_start_statement_parse (JSP_STATE_STAT_SWITCH_BRANCH_EXPR);
      jsp_state_top()->u.statement.u.switch_statement.case_clause_count = 0;
      jsp_state_top()->u.statement.u.switch_statement.loc = start_loc;
      jsp_state_top()->u.statement.u.switch_statement.jmp_oc = MAX_OPCODES;
      jsp_state_top()->u.statement.u.switch_statement.expr = switch_expr;
    }
    else if (state_p->state == JSP_STATE_STAT_SWITCH_BRANCH_EXPR)
    {
      if (is_subexpr_end)
      {
        jsp_operand_t case_expr = dump_get_value_if_value_based_ref (subexpr_operand,
                                                                     subexpr_prop_name_operand,
                                                                     is_subexpr_value_based_reference);

        current_token_must_be (TOK_COLON);

        jsp_operand_t switch_expr = state_p->u.statement.u.switch_statement.expr;

        const jsp_operand_t cond = tmp_operand ();
        dump_equal_value_type (cond, switch_expr, case_expr);

        vm_instr_counter_t jmp_oc = dump_case_clause_check_for_rewrite (cond);
        skip_token ();

        jsp_state_t tmp_state = *state_p;
        jsp_state_pop ();
        jsp_start_statement_parse (JSP_STATE_STAT_SWITCH_BRANCH);
        jsp_state_top ()->u.statement.u.switch_statement.loc = tok.loc;
        jsp_state_top ()->u.statement.u.switch_statement.jmp_oc = jmp_oc;
        jsp_state_push (tmp_state);
        state_p = jsp_state_top ();

        skip_case_clause_body ();
      }

      if (token_is (TOK_KW_CASE) || token_is (TOK_KW_DEFAULT))
      {
        state_p->u.statement.u.switch_statement.case_clause_count++;

        if (token_is (TOK_KW_CASE))
        {
          skip_token ();
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
        }
        else if (token_is (TOK_KW_DEFAULT))
        {
          if (state_p->was_default)
          {
            EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Duplication of 'default' clause");
          }
          state_p->was_default = true;

          skip_token ();

          current_token_must_be_check_and_skip_it (TOK_COLON);

          jsp_state_t tmp_state = *state_p;
          jsp_state_pop ();
          jsp_start_statement_parse (JSP_STATE_STAT_SWITCH_BRANCH);
          jsp_state_top ()->u.statement.u.switch_statement.loc = tok.loc;
          jsp_state_top ()->u.statement.u.switch_statement.jmp_oc = MAX_OPCODES;
          jsp_state_top ()->is_default_branch = true;
          jsp_state_push (tmp_state);
          state_p = jsp_state_top ();

          skip_case_clause_body ();
        }
      }
      else
      {
        current_token_must_be (TOK_CLOSE_BRACE);

        vm_instr_counter_t jmp_oc = dump_default_clause_check_for_rewrite ();

        /**
         * Reorder switch branches here, so that they are processed in reverse stack push order
         */
        uint16_t case_clause_count = state_p->u.statement.u.switch_statement.case_clause_count;
        locus start_loc = state_p->u.statement.u.switch_statement.loc;
        bool was_default = state_p->was_default;
        jsp_state_pop ();

        JERRY_ASSERT (jsp_state_stack_pos >= case_clause_count);
        for (uint16_t i = 0; i < case_clause_count / 2; ++i)
        {
          jsp_state_t *tmp_state1_p = &jsp_state_stack [jsp_state_stack_pos - case_clause_count + i];
          JERRY_ASSERT (tmp_state1_p->state == JSP_STATE_STAT_SWITCH_BRANCH);

          jsp_state_t *tmp_state2_p = &jsp_state_stack [jsp_state_stack_pos - 1 - i];
          JERRY_ASSERT (tmp_state2_p->state == JSP_STATE_STAT_SWITCH_BRANCH);

          locus loc = tmp_state1_p->u.statement.u.switch_statement.loc;
          tmp_state1_p->u.statement.u.switch_statement.loc = tmp_state2_p->u.statement.u.switch_statement.loc;
          tmp_state2_p->u.statement.u.switch_statement.loc = loc;

          bool is_default_branch = tmp_state1_p->is_default_branch;
          tmp_state1_p->is_default_branch = tmp_state2_p->is_default_branch;
          tmp_state2_p->is_default_branch = is_default_branch;

          vm_instr_counter_t jmp_oc_tmp = tmp_state1_p->u.statement.u.switch_statement.jmp_oc;
          tmp_state1_p->u.statement.u.switch_statement.jmp_oc = tmp_state2_p->u.statement.u.switch_statement.jmp_oc;
          tmp_state2_p->u.statement.u.switch_statement.jmp_oc = jmp_oc_tmp;
        }

        for (uint16_t i = 0; i < case_clause_count; i++)
        {
          if (jsp_state_stack [jsp_state_stack_pos - case_clause_count + i].is_default_branch)
          {
            JERRY_ASSERT (jsp_state_stack [jsp_state_stack_pos - case_clause_count + i].u.statement.u.switch_statement.jmp_oc == MAX_OPCODES);
            jsp_state_stack [jsp_state_stack_pos - case_clause_count + i].u.statement.u.switch_statement.jmp_oc = jmp_oc;
          }
        }

        /**
         * Mark final state if default branch was seen
         */
        jsp_state_t *tmp_state_p = &jsp_state_stack [jsp_state_stack_pos - case_clause_count - 1];
        JERRY_ASSERT (tmp_state_p->state == JSP_STATE_STAT_SWITCH_FINISH);
        tmp_state_p->was_default = was_default;

        if (!was_default)
        {
          tmp_state_p->u.statement.u.switch_statement.jmp_oc = jmp_oc;
        }

        seek_token (start_loc);

        // Second, parse case clauses' bodies and rewrite jumps
        current_token_must_be_check_and_skip_it (TOK_OPEN_BRACE);
      }
    }
    else if (state_p->state == JSP_STATE_STAT_SWITCH_BRANCH)
    {
      seek_token (state_p->u.statement.u.switch_statement.loc);

      if (state_p->is_default_branch)
      {
        rewrite_default_clause (state_p->u.statement.u.switch_statement.jmp_oc);

        if (token_is (TOK_KW_CASE))
        {
          JSP_COMPLETE_STATEMENT_PARSE ();
          continue;
        }
      }
      else
      {
        rewrite_case_clause (state_p->u.statement.u.switch_statement.jmp_oc);
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
      if (!state_p->was_default)
      {
        rewrite_default_clause (state_p->u.statement.u.switch_statement.jmp_oc);
      }

      current_token_must_be_check_and_skip_it (TOK_CLOSE_BRACE);

      finish_dumping_case_clauses ();

      JSP_COMPLETE_STATEMENT_PARSE ();
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
        const jsp_operand_t expr = subexpr_operand;

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

      jsp_operand_t expr = dump_get_value_if_ref (subexpr_operand,
                                                  subexpr_prop_name_operand,
                                                  is_subexpr_value_based_reference);

      if (dumper_get_scope ()->type == SCOPE_TYPE_EVAL)
      {
        dump_variable_assignment (jsp_operand_t::make_reg_operand (VM_REG_SPECIAL_EVAL_RET),
                                  expr);
      }

      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else if (state_p->state == JSP_STATE_STAT_RETURN)
    {
      JERRY_ASSERT (is_subexpr_end);

      const jsp_operand_t op = dump_get_value_if_value_based_ref (subexpr_operand,
                                                                  subexpr_prop_name_operand,
                                                                  is_subexpr_value_based_reference);
      dump_retval (op);

      insert_semicolon ();

      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else if (state_p->state == JSP_STATE_STAT_THROW)
    {
      JERRY_ASSERT (is_subexpr_end);

      const jsp_operand_t op = dump_get_value_if_value_based_ref (subexpr_operand,
                                                                  subexpr_prop_name_operand,
                                                                  is_subexpr_value_based_reference);
      dump_throw (op);

      insert_semicolon ();

      JSP_COMPLETE_STATEMENT_PARSE ();
    }
    else
    {
      JERRY_ASSERT (state_p->state == JSP_STATE_STAT_STATEMENT);
      JERRY_ASSERT (!state_p->is_completed);

      vm_instr_counter_t *rewrite_chain_p = &state_p->u.statement.breaks_rewrite_chain;
      vm_instr_counter_t break_tgt_oc = dumper_get_current_instr_counter ();
      if (is_generate_bytecode)
      {
        while (*rewrite_chain_p != MAX_OPCODES)
        {
          *rewrite_chain_p = rewrite_simple_or_nested_jump_and_get_next (*rewrite_chain_p,
                                                                         break_tgt_oc);
        }
      }

      state_p->is_completed = true;
    }
  }
} /* jsp_parse_source_element_list */

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

    jsp_parse_source_element_list ();

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
                                                          parser_show_instrs,
                                                          is_generate_bytecode);

    dumper_free ();

    if (out_contains_functions_p != NULL)
    {
      *out_contains_functions_p = scope->contains_functions;
    }

    dumper_set_scope (NULL);
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
                     const bytecode_data_header_t **out_bytecode_data_p, /**< out: generated byte-code array
                                                                          *  (in case there were no syntax errors) */
                     jsp_parse_mode_t parse_mode)
{
  if (parse_mode == PARSE_MODE_PREPARSE)
  {
    is_generate_bytecode = false;
    dumper_set_generate_bytecode (false);
    scopes_tree_set_generate_bytecode (false);
  }
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
