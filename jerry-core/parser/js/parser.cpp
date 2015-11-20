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

typedef enum
{
  JSP_STATE_EXPR_UNINITIALIZED  = 0x0000,

  /** Mask of expression type field */
  JSP_STATE_EXPR_TYPE_MASK      = 0x00ff,

  /* ECMA-262 v5 expression types */
  JSP_STATE_EXPR_EMPTY              = 0x01, /**< no expression yet (at start) */
  JSP_STATE_EXPR_FUNCTION           = 0x03, /**< FunctionExpression (11.2.5) */
  JSP_STATE_EXPR_MEMBER             = 0x04, /**< MemberExpression (11.2) */
  JSP_STATE_EXPR_CALL               = 0x06, /**< CallExpression (11.2) */
  JSP_STATE_EXPR_LEFTHANDSIDE       = 0x07, /**< LeftHandSideExpression (11.2) */
  JSP_STATE_EXPR_POSTFIX            = 0x08, /**< PostfixExpression (11.3) */
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
  JSP_STATE_STAT_VAR_DECL           = 0x35,
} jsp_state_expr_t;

static jsp_operand_t parse_expression_ (jsp_state_expr_t, bool);

static jsp_operand_t parse_expression (bool, jsp_eval_ret_store_t);

static void parse_statement (jsp_label_t *outermost_stmt_label_p);
static void parse_source_element_list (void);

static bool
token_is (token_type tt)
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

static void
assert_keyword (keyword kw)
{
  if (!token_is (TOK_KEYWORD) || token_data () != kw)
  {
    EMIT_ERROR_VARG (JSP_EARLY_ERROR_SYNTAX, "Expected keyword '%s'", lexer_keyword_to_string (kw));
    JERRY_UNREACHABLE ();
  }
}

static bool
is_keyword (keyword kw)
{
  return token_is (TOK_KEYWORD) && token_data () == kw;
}

static void
current_token_must_be (token_type tt)
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
jsp_skip_braces (token_type brace_type) /**< type of the opening brace */
{
  current_token_must_be (brace_type);

  token_type closing_bracket_type;

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
jsp_find_next_token_before_the_locus (token_type token_to_find, /**< token to search for (except TOK_EOF) */
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
  switch (lexer_get_token_type (tok))
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
    case TOK_KEYWORD:
    {
      const char *s = lexer_keyword_to_string ((keyword) token_data ());
      literal_t lit = lit_find_or_create_literal_from_utf8_string ((const lit_utf8_byte_t *) s,
                                                                   (lit_utf8_size_t)strlen (s));
      return literal_operand (lit_cpointer_t::compress (lit));
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

  if (lit_utf8_iterator_pos_cmp (start_loc, tok.loc) != 0)
  {
    lexer_seek (start_loc);
  }
  else
  {
    lexer_save_token (tok);
  }
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
  dump_varg_header_for_rewrite (is_function_expression ? VARG_FUNC_EXPR : VARG_FUNC_DECL, func_name);

  while (!token_is (TOK_CLOSE_PAREN))
  {
    dumper_start_varg_code_sequence ();

    current_token_must_be (TOK_NAME);
    jsp_operand_t formal_parameter_name = literal_operand (token_data_as_lit_cp ());
    skip_token ();

    jsp_early_error_add_varg (formal_parameter_name);
    dump_varg (formal_parameter_name);

    formal_parameters_num++;

    dumper_finish_varg_code_sequence ();

    if (token_is (TOK_COMMA))
    {
      skip_token ();
    }
    else
    {
      current_token_must_be (TOK_CLOSE_PAREN);
    }
  }

  const jsp_operand_t func = rewrite_varg_header_set_args_count (formal_parameters_num);

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

  skip_token ();
  current_token_must_be (TOK_CLOSE_BRACE);

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

/* function_declaration
  : 'function' LT!* Identifier LT!*
    '(' (LT!* Identifier (LT!* ',' LT!* Identifier)*) ? LT!* ')' LT!* function_body
  ;

   function_body
  : '{' LT!* sourceElements LT!* '}' */
static void
parse_function_declaration (void)
{
  assert_keyword (KW_FUNCTION);
  skip_token ();

  current_token_must_be (TOK_NAME);

  const jsp_operand_t func_name = literal_operand (token_data_as_lit_cp ());
  skip_token ();

  jsp_start_parse_function_scope (func_name, false, NULL);

  parse_source_element_list ();

  jsp_finish_parse_function_scope (false);
}

typedef enum
{
  JSP_OPERATOR_NO_OP,

  JSP_OPERATOR_COMMA,

  JSP_OPERATOR_QUERY,
  JSP_OPERATOR_COLON,

  JSP_OPERATOR_LOGICAL_OR,
  JSP_OPERATOR_LOGICAL_AND,

  JSP_OPERATOR_DELETE,
  JSP_OPERATOR_VOID,
  JSP_OPERATOR_TYPEOF,
  JSP_OPERATOR_PREINCR,
  JSP_OPERATOR_PREDECR,
  JSP_OPERATOR_PLUS,
  JSP_OPERATOR_MINUS,
  JSP_OPERATOR_INVERT,
  JSP_OPERATOR_NOT,

  JSP_OPERATOR_B_AND,
  JSP_OPERATOR_B_XOR,
  JSP_OPERATOR_B_OR,

  JSP_OPERATOR_ADD,
  JSP_OPERATOR_SUB,

  JSP_OPERATOR_MUL,
  JSP_OPERATOR_DIV,
  JSP_OPERATOR_MOD,

  JSP_OPERATOR_LSHIFT,
  JSP_OPERATOR_RSHIFT,
  JSP_OPERATOR_RSHIFT_U,

  JSP_OPERATOR_ASSIGN,

  JSP_OPERATOR_ASSIGN_B_AND,
  JSP_OPERATOR_ASSIGN_B_XOR,
  JSP_OPERATOR_ASSIGN_B_OR,

  JSP_OPERATOR_ASSIGN_ADD,
  JSP_OPERATOR_ASSIGN_SUB,

  JSP_OPERATOR_ASSIGN_MUL,
  JSP_OPERATOR_ASSIGN_DIV,
  JSP_OPERATOR_ASSIGN_MOD,

  JSP_OPERATOR_ASSIGN_LSHIFT,
  JSP_OPERATOR_ASSIGN_RSHIFT,
  JSP_OPERATOR_ASSIGN_RSHIFT_U,

  JSP_OPERATOR_EQUAL,
  JSP_OPERATOR_NOT_EQUAL,
  JSP_OPERATOR_STRICT_EQUAL,
  JSP_OPERATOR_STRICT_NOT_EQUAL,

  JSP_OPERATOR_LESS,
  JSP_OPERATOR_GREATER,
  JSP_OPERATOR_LESS_OR_EQUAL,
  JSP_OPERATOR_GREATER_OR_EQUAL,
  JSP_OPERATOR_INSTANCEOF,
  JSP_OPERATOR_IN,

  JSP_OPERATOR_PROP_ACCESSOR,

  JSP_OPERATOR_GROUP,

  JSP_OPERATOR_NEW,
} jsp_operator_t;

typedef enum
{
  /* Flags */
  JSP_STATE_EXPR_FLAG_NO_FLAGS           = 0x0000, /**< empty flags set */
  JSP_STATE_EXPR_FLAG_COMPLETED          = 0x0100, /**< the expression parse completed, no more tokens can be added to
                                                    *   the expression */
  JSP_STATE_EXPR_FLAG_ARG_LIST           = 0x0200, /**< parsing an argument list, associated with the expression */
  JSP_STATE_EXPR_FLAG_ARG_COMPLETED      = 0x0400, /**< parse of a next argument completed */
  JSP_STATE_EXPR_FLAG_NO_IN              = 0x0800, /**< expression is parsed in NoIn mode
                                                    *   (see also: ECMA-262 v5, 11.8) */
  JSP_STATE_EXPR_FLAG_FIXED_RET_OPERAND  = 0x1000, /**< the expression's evaluation should produce value that should be
                                                    *   put to register, specified by operand, specified in state */
  JSP_STATE_EXPR_FLAG_COMPLEX_PRODUCTION = 0x2000, /**< parse of a next argument completed */
} jsp_state_expr_flag_t;

typedef struct
{
  jsp_operand_t operand; /**< operand, associated with expression */
  vm_instr_counter_t rewrite_chain; /**< chain of jmp instructions to rewrite */
  jsp_state_expr_t state; /**< current state */
  jsp_state_expr_t req_expr_type; /**< requested type of expression */
  int flags; /**< flags */
  jsp_operator_t op; /**< operator, applied to current and, if binary, to previous expression */
  struct /* FIXME: switch to union */
  {
    uint32_t arg_list_length; /**< length of arguments list associated with the expression
                               *   (valid only if JSP_STATE_EXPR_FLAG_ARG_LIST flag is set) */
    struct
    {
      jsp_operand_t prop_name;
      bool is_setter;
    } accessor_prop_decl;
  } u;
} jsp_state_t;

/* FIXME: change to dynamic */
#define JSP_STATE_STACK_MAX 128
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

static jsp_state_t
jsp_state_top (void)
{
  JERRY_ASSERT (jsp_state_stack_pos > 0);

  return jsp_state_stack[jsp_state_stack_pos - 1u];
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
  new_state.op = JSP_OPERATOR_NO_OP;
  new_state.rewrite_chain = MAX_OPCODES; /* empty chain */
  new_state.flags = JSP_STATE_EXPR_FLAG_NO_FLAGS;

  if (!in_allowed)
  {
    new_state.flags |= JSP_STATE_EXPR_FLAG_NO_IN;
  }

  jsp_state_push (new_state);
} /* jsp_push_new_expr_state */

/*
 * FIXME:
 *       Move to dumper
 */
static void
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
  dump_varg_header_for_rewrite (VARG_CALL_EXPR, val);

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
} /* jsp_start_call_dump */

/*
 * FIXME:
 *       Move to dumper
 */
static jsp_operand_t
jsp_finish_call_dump (uint32_t args_num)
{
  return rewrite_varg_header_set_args_count (args_num);
} /* jsp_finish_call_dump */

/*
 * FIXME:
 *       Move to dumper
 */
static void __attr_unused___
jsp_start_construct_dump (jsp_operand_t obj)
{
  dump_varg_header_for_rewrite (VARG_CONSTRUCT_EXPR, dump_assignment_of_lhs_if_value_based_reference (obj));
} /* jsp_start_construct_dump */

/*
 * FIXME:
 *       Move to dumper
 */
static jsp_operand_t __attr_unused___
jsp_finish_construct_dump (uint32_t args_num)
{
  return rewrite_varg_header_set_args_count (args_num);
} /* jsp_finish_construct_dump */

static lit_cpointer_t
jsp_get_prop_name_after_dot (void)
{
  if (token_is (TOK_NAME))
  {
    return token_data_as_lit_cp ();
  }
  else if (token_is (TOK_KEYWORD))
  {
    const char *s = lexer_keyword_to_string ((keyword) token_data ());
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
  uint32_t start_pos = jsp_state_stack_pos;

  jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, req_expr, in_allowed);

  while (true)
  {
    jsp_state_t state, subexpr_state;

    state = jsp_state_top ();
    jsp_state_pop ();

    bool is_subexpr_end = false;

    if (state.state == state.req_expr_type
        && ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0))
    {
      (void) jsp_is_stack_empty ();

      if (start_pos == jsp_state_stack_pos) // FIXME: jsp_is_stack_empty ()
      {
        lexer_save_token (tok);

        /* expression parse finished */
        return state.operand;
      }
      else
      {
        is_subexpr_end = true;

        subexpr_state = state;

        state = jsp_state_top ();
        jsp_state_pop ();

        JERRY_ASSERT ((subexpr_state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0);
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
      JERRY_ASSERT (!(state.state == JSP_STATE_EXPR_EXPRESSION && state.req_expr_type != JSP_STATE_EXPR_EXPRESSION));
    }

    const bool in_allowed = ((state.flags & JSP_STATE_EXPR_FLAG_NO_IN) == 0);

    if (state.state == JSP_STATE_EXPR_EMPTY)
    {
      /* no subexpressions can occur, as expression parse is just started */
      JERRY_ASSERT (!is_subexpr_end);
      JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) == 0);

      token_type tt = lexer_get_token_type (tok);
      if (tt == TOK_DOUBLE_PLUS
          || tt == TOK_DOUBLE_MINUS
          || tt == TOK_PLUS
          || tt == TOK_MINUS
          || tt == TOK_COMPL
          || tt == TOK_NOT
          || (tt == TOK_KEYWORD
              && (is_keyword (KW_DELETE)
                  || is_keyword (KW_VOID)
                  || is_keyword (KW_TYPEOF))))
      {
        /* ECMA-262 v5, 11.4 */
        state.state = JSP_STATE_EXPR_UNARY;

        if (tt == TOK_DOUBLE_PLUS)
        {
          state.op = JSP_OPERATOR_PREINCR;
        }
        else if (tt == TOK_DOUBLE_MINUS)
        {
          state.op = JSP_OPERATOR_PREDECR;
        }
        else if (tt == TOK_PLUS)
        {
          state.op = JSP_OPERATOR_PLUS;
        }
        else if (tt == TOK_MINUS)
        {
          state.op = JSP_OPERATOR_MINUS;
        }
        else if (tt == TOK_COMPL)
        {
          state.op = JSP_OPERATOR_INVERT;
        }
        else if (tt == TOK_NOT)
        {
          state.op = JSP_OPERATOR_NOT;
        }
        else
        {
          JERRY_ASSERT (tt == TOK_KEYWORD);

          if (is_keyword (KW_DELETE))
          {
            state.op = JSP_OPERATOR_DELETE;

            scopes_tree_set_contains_delete (serializer_get_scope ());
          }
          else if (is_keyword (KW_VOID))
          {
            state.op = JSP_OPERATOR_VOID;
          }
          else
          {
            JERRY_ASSERT (is_keyword (KW_TYPEOF));

            state.op = JSP_OPERATOR_TYPEOF;
          }
        }

        skip_token ();

        jsp_state_push (state);
        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_UNARY, in_allowed);
      }
      else if (token_is (TOK_KEYWORD) && is_keyword (KW_FUNCTION))
      {
        state.state = JSP_STATE_EXPR_FUNCTION;
        jsp_state_push (state);
      }
      else if (token_is (TOK_KEYWORD) && is_keyword (KW_NEW))
      {
        skip_token ();

        state.state = JSP_STATE_EXPR_MEMBER;
        state.op = JSP_OPERATOR_NEW;

        jsp_state_push (state);
        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_MEMBER, true);
      }
      else if (token_is (TOK_OPEN_SQUARE))
      {
        skip_token ();

        dump_varg_header_for_rewrite (VARG_ARRAY_DECL, empty_operand ());

        state.state = JSP_STATE_EXPR_ARRAY_LITERAL;
        state.flags |= JSP_STATE_EXPR_FLAG_ARG_LIST;
        state.u.arg_list_length = 0;

        jsp_state_push (state);
      }
      else if (token_is (TOK_OPEN_BRACE))
      {
        skip_token ();

        dump_varg_header_for_rewrite (VARG_OBJ_DECL, empty_operand ());
        jsp_early_error_start_checking_of_prop_names ();

        state.state = JSP_STATE_EXPR_OBJECT_LITERAL;
        state.flags |= JSP_STATE_EXPR_FLAG_ARG_LIST;
        state.u.arg_list_length = 0;

        jsp_state_push (state);
      }
      else
      {
        if (token_is (TOK_OPEN_PAREN))
        {
          skip_token ();

          state.state = JSP_STATE_EXPR_MEMBER;
          state.op = JSP_OPERATOR_GROUP;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
        }
        else
        {
          state.state = JSP_STATE_EXPR_MEMBER;

          if (token_is (TOK_KEYWORD) && is_keyword (KW_THIS))
          {
            state.operand = dump_this_res ();
          }
          else
          {
            if (lexer_get_token_type (tok) == TOK_DIV || lexer_get_token_type (tok) == TOK_DIV_EQ)
            {
              rescan_regexp_token ();

              current_token_must_be (TOK_REGEXP);

              state.operand = dump_regexp_assignment_res (token_data_as_lit_cp ());
            }
            else
            {
              switch (lexer_get_token_type (tok))
              {
                case TOK_NULL:
                {
                  state.operand = dump_null_assignment_res ();
                  break;
                }
                case TOK_BOOL:
                {
                  state.operand = dump_boolean_assignment_res ((bool) token_data ());
                  break;
                }
                case TOK_SMALL_INT:
                {
                  state.operand = dump_smallint_assignment_res ((vm_idx_t) token_data ());
                  break;
                }
                case TOK_NUMBER:
                {
                  state.operand = dump_number_assignment_res (token_data_as_lit_cp ());
                  break;
                }
                case TOK_STRING:
                {
                  state.operand = dump_string_assignment_res (token_data_as_lit_cp ());
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

                  state.operand = jsp_operand_t::make_identifier_operand (token_data_as_lit_cp ());

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
          }

          skip_token ();
          jsp_state_push (state);
        }
      }
    }
    else if (state.state == JSP_STATE_STAT_STATEMENT_LIST)
    {
      JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) == 0);

      /* FIXME: merge with parse_statement_ */
      parse_source_element_list ();

      state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;
      jsp_state_push (state);
    }
    else if (state.state == JSP_STATE_EXPR_FUNCTION)
    {
      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        state.state = JSP_STATE_EXPR_MEMBER;
        state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLETED;

        jsp_state_push (state);
      }
      else
      {
        if (is_subexpr_end)
        {
          jsp_finish_parse_function_scope (true);

          skip_token ();

          state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

          jsp_state_push (state);
        }
        else
        {
          assert_keyword (KW_FUNCTION);
          skip_token ();

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

          state.operand = jsp_start_parse_function_scope (name, true, NULL);

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_STAT_STATEMENT_LIST, JSP_STATE_STAT_STATEMENT_LIST, true);
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_DATA_PROP_DECL)
    {
      JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) == 0);

      if (is_subexpr_end)
      {
        JERRY_ASSERT (subexpr_state.state == JSP_STATE_EXPR_ASSIGNMENT);

        jsp_operand_t prop_name = state.operand;
        jsp_operand_t value = subexpr_state.operand;

        JERRY_ASSERT (prop_name.is_literal_operand ());

        dump_prop_name_and_value (prop_name, dump_assignment_of_lhs_if_value_based_reference (value));
        jsp_early_error_add_prop_name (prop_name, PROP_DATA);

        state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;
        jsp_state_push (state);
      }
      else
      {
        JERRY_ASSERT (state.operand.is_empty_operand ());
        state.operand = parse_property_name ();
        skip_token ();

        JERRY_ASSERT (token_is (TOK_COLON));
        skip_token ();

        jsp_state_push (state);
        jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);
      }
    }
    else if (state.state == JSP_STATE_EXPR_ACCESSOR_PROP_DECL)
    {
      JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) == 0);

      if (is_subexpr_end)
      {
        jsp_finish_parse_function_scope (true);

        skip_token ();

        jsp_operand_t prop_name = state.u.accessor_prop_decl.prop_name;
        jsp_operand_t func = state.operand;
        bool is_setter = state.u.accessor_prop_decl.is_setter;

        if (is_setter)
        {
          dump_prop_setter_decl (prop_name, func);
        }
        else
        {
          dump_prop_getter_decl (prop_name, func);
        }

        state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;
        jsp_state_push (state);
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

        JERRY_ASSERT (state.operand.is_empty_operand ());
        state.operand = func;

        state.u.accessor_prop_decl.prop_name = prop_name;
        state.u.accessor_prop_decl.is_setter = is_setter;

        jsp_state_push (state);
        jsp_push_new_expr_state (JSP_STATE_STAT_STATEMENT_LIST, JSP_STATE_STAT_STATEMENT_LIST, true);
      }
    }
    else if (state.state == JSP_STATE_EXPR_OBJECT_LITERAL)
    {
      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        JERRY_ASSERT (!is_subexpr_end);

        state.state = JSP_STATE_EXPR_MEMBER;
        state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLETED;

        jsp_state_push (state);
      }
      else
      {
        JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_ARG_LIST) != 0);

        if (is_subexpr_end)
        {
          JERRY_ASSERT (subexpr_state.state == JSP_STATE_EXPR_DATA_PROP_DECL
                        || subexpr_state.state == JSP_STATE_EXPR_ACCESSOR_PROP_DECL);

          state.u.arg_list_length++;

          dumper_finish_varg_code_sequence ();

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

          state.operand = rewrite_varg_header_set_args_count (state.u.arg_list_length);

          state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;
          state.flags &= ~JSP_STATE_EXPR_FLAG_ARG_LIST;

          jsp_state_push (state);
        }
        else
        {
          dumper_start_varg_code_sequence ();

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

          jsp_state_push (state);
          jsp_push_new_expr_state (expr_type, expr_type, true);
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_ARRAY_LITERAL)
    {
      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        JERRY_ASSERT (!is_subexpr_end);

        state.state = JSP_STATE_EXPR_MEMBER;
        state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLETED;

        jsp_state_push (state);
      }
      else
      {
        JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_ARG_LIST) != 0);

        if (is_subexpr_end)
        {
          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);

          dump_varg (subexpr_state.operand);

          state.u.arg_list_length++;

          dumper_finish_varg_code_sequence ();

          jsp_state_push (state);

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

            state.operand = rewrite_varg_header_set_args_count (state.u.arg_list_length);

            state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;
            state.flags &= ~JSP_STATE_EXPR_FLAG_ARG_LIST;

            jsp_state_push (state);
          }
          else if (token_is (TOK_COMMA))
          {
            while (token_is (TOK_COMMA))
            {
              skip_token ();

              dumper_start_varg_code_sequence ();

              dump_varg (dump_array_hole_assignment_res ());

              state.u.arg_list_length++;

              dumper_finish_varg_code_sequence ();
            }

            jsp_state_push (state);
          }
          else
          {
            jsp_state_push (state);

            dumper_start_varg_code_sequence ();

            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);
          }
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_MEMBER)
    {
      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        if (token_is (TOK_OPEN_PAREN))
        {
          state.state = JSP_STATE_EXPR_CALL;
          state.flags &= ~(JSP_STATE_EXPR_FLAG_COMPLETED);

          /* propagate to CallExpression */
          state.state = JSP_STATE_EXPR_CALL;
        }
        else
        {
          /* propagate to LeftHandSideExpression */
          state.state = JSP_STATE_EXPR_LEFTHANDSIDE;
        }

        jsp_state_push (state);
      }
      else
      {
        if (is_subexpr_end)
        {
          if ((state.flags & JSP_STATE_EXPR_FLAG_ARG_LIST) != 0)
          {
            JERRY_ASSERT (state.op == JSP_OPERATOR_NEW);
            JERRY_ASSERT (subexpr_state.state == JSP_STATE_EXPR_ASSIGNMENT);

            subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);
            dump_varg (subexpr_state.operand);

            dumper_finish_varg_code_sequence ();

            state.u.arg_list_length++;

            if (token_is (TOK_CLOSE_PAREN))
            {
              state.op = JSP_OPERATOR_NO_OP;
              state.flags &= ~JSP_STATE_EXPR_FLAG_ARG_LIST;
              state.operand = jsp_finish_construct_dump (state.u.arg_list_length);

              jsp_state_push (state);
            }
            else
            {
              current_token_must_be (TOK_COMMA);

              jsp_state_push (state);
              jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);

              dumper_start_varg_code_sequence ();
            }

            skip_token ();
          }
          else if (state.op == JSP_OPERATOR_GROUP)
          {
            JERRY_ASSERT (state.operand.is_empty_operand ());

            state.operand = subexpr_state.operand;
            state.op = JSP_OPERATOR_NO_OP;

            current_token_must_be (TOK_CLOSE_PAREN);
            skip_token ();

            jsp_state_push (state);
          }
          else if (state.op == JSP_OPERATOR_NEW)
          {
            JERRY_ASSERT (subexpr_state.state == JSP_STATE_EXPR_MEMBER);
            JERRY_ASSERT (state.operand.is_empty_operand ());
            JERRY_ASSERT (!subexpr_state.operand.is_empty_operand ());

            state.operand = subexpr_state.operand;

            jsp_start_construct_dump (state.operand);

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
              state.flags |= JSP_STATE_EXPR_FLAG_ARG_LIST;
              state.u.arg_list_length = 0;
              jsp_state_push (state);

              dumper_start_varg_code_sequence ();
              jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);
            }
            else
            {
              state.op = JSP_OPERATOR_NO_OP;

              if (is_arg_list_implicit)
              {
                state.state = JSP_STATE_EXPR_MEMBER;
                state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;
              }

              state.operand = jsp_finish_construct_dump (0);

              jsp_state_push (state);
            }
          }
          else
          {
            JERRY_ASSERT (state.op == JSP_OPERATOR_PROP_ACCESSOR);
            state.op = JSP_OPERATOR_NO_OP;

            current_token_must_be (TOK_CLOSE_SQUARE);
            skip_token ();

            subexpr_state.operand = dump_assignment_of_lhs_if_reference (subexpr_state.operand);

            if (state.operand.is_identifier_operand ())
            {
              state.operand = jsp_operand_t::make_value_based_ref_operand_lv (state.operand.get_identifier_name (),
                                                                              subexpr_state.operand);
            }
            else
            {
              state.operand = jsp_operand_t::make_value_based_ref_operand_vv (state.operand, subexpr_state.operand);
            }

            jsp_state_push (state);
          }
        }
        else if (token_is (TOK_OPEN_SQUARE))
        {
          skip_token ();

          state.op = JSP_OPERATOR_PROP_ACCESSOR;
          state.operand = dump_assignment_of_lhs_if_value_based_reference (state.operand);

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
        }
        else if (token_is (TOK_DOT))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_value_based_reference (state.operand);

          if (state.operand.is_identifier_operand ())
          {
            state.operand = jsp_operand_t::make_value_based_ref_operand_ll (state.operand.get_identifier_name (),
                                                                            jsp_get_prop_name_after_dot ());
          }
          else
          {
            state.operand = jsp_operand_t::make_value_based_ref_operand_vl (state.operand,
                                                                            jsp_get_prop_name_after_dot ());
          }

          jsp_state_push (state);

          skip_token ();
        }
        else
        {
          state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

          jsp_state_push (state);
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_CALL)
    {
      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        /* propagate to LeftHandSideExpression */
        state.state = JSP_STATE_EXPR_LEFTHANDSIDE;

        jsp_state_push (state);
      }
      else
      {
        if (is_subexpr_end)
        {
          if ((state.flags & JSP_STATE_EXPR_FLAG_ARG_LIST) != 0)
          {
            JERRY_ASSERT (subexpr_state.state == JSP_STATE_EXPR_ASSIGNMENT);

            subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);
            dump_varg (subexpr_state.operand);

            dumper_finish_varg_code_sequence ();

            state.u.arg_list_length++;

            if (token_is (TOK_CLOSE_PAREN))
            {
              state.flags &= ~JSP_STATE_EXPR_FLAG_ARG_LIST;

              state.operand = jsp_finish_call_dump (state.u.arg_list_length);

              jsp_state_push (state);
            }
            else
            {
              current_token_must_be (TOK_COMMA);

              jsp_state_push (state);
              jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);

              dumper_start_varg_code_sequence ();
            }

            skip_token ();
          }
          else
          {
            JERRY_ASSERT (state.op == JSP_OPERATOR_PROP_ACCESSOR);
            state.op = JSP_OPERATOR_NO_OP;

            current_token_must_be (TOK_CLOSE_SQUARE);
            skip_token ();

            subexpr_state.operand = dump_assignment_of_lhs_if_reference (subexpr_state.operand);
            state.operand = jsp_operand_t::make_value_based_ref_operand_vv (state.operand,
                                                                            subexpr_state.operand);

            jsp_state_push (state);
          }
        }
        else
        {
          if (token_is (TOK_OPEN_PAREN))
          {
            skip_token ();

            jsp_start_call_dump (state.operand);

            if (!token_is (TOK_CLOSE_PAREN))
            {
              state.flags |= JSP_STATE_EXPR_FLAG_ARG_LIST;
              state.u.arg_list_length = 0;
              jsp_state_push (state);

              dumper_start_varg_code_sequence ();

              jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);
            }
            else
            {
              skip_token ();

              state.operand = jsp_finish_call_dump (0);
              jsp_state_push (state);
            }
          }
          else if (token_is (TOK_OPEN_SQUARE))
          {
            skip_token ();

            state.op = JSP_OPERATOR_PROP_ACCESSOR;
            state.operand = dump_assignment_of_lhs_if_reference (state.operand);

            jsp_state_push (state);
            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EXPRESSION, true);
          }
          else if (token_is (TOK_DOT))
          {
            skip_token ();

            state.operand = dump_assignment_of_lhs_if_reference (state.operand);

            state.operand = jsp_operand_t::make_value_based_ref_operand_vl (state.operand,
                                                                            jsp_get_prop_name_after_dot ());

            jsp_state_push (state);

            skip_token ();
          }
          else
          {
            state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

            jsp_state_push (state);
          }
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_LEFTHANDSIDE)
    {
      if (is_subexpr_end)
      {
        jsp_operator_t op = state.op;

        state.state = JSP_STATE_EXPR_ASSIGNMENT;
        state.op = JSP_OPERATOR_NO_OP;
        state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

        JERRY_ASSERT (op == JSP_OPERATOR_ASSIGN
                      || op == JSP_OPERATOR_ASSIGN_MUL
                      || op == JSP_OPERATOR_ASSIGN_DIV
                      || op == JSP_OPERATOR_ASSIGN_MOD
                      || op == JSP_OPERATOR_ASSIGN_ADD
                      || op == JSP_OPERATOR_ASSIGN_SUB
                      || op == JSP_OPERATOR_ASSIGN_LSHIFT
                      || op == JSP_OPERATOR_ASSIGN_RSHIFT
                      || op == JSP_OPERATOR_ASSIGN_RSHIFT_U
                      || op == JSP_OPERATOR_ASSIGN_B_AND
                      || op == JSP_OPERATOR_ASSIGN_B_XOR
                      || op == JSP_OPERATOR_ASSIGN_B_OR);

        subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);

        if (op == JSP_OPERATOR_ASSIGN)
        {
          state.operand = dump_prop_setter_or_variable_assignment_res (state.operand, subexpr_state.operand);
        }
        else if (op == JSP_OPERATOR_ASSIGN_MUL)
        {
          state.operand = dump_prop_setter_or_multiplication_res (state.operand, subexpr_state.operand);
        }
        else if (op == JSP_OPERATOR_ASSIGN_DIV)
        {
          state.operand = dump_prop_setter_or_division_res (state.operand, subexpr_state.operand);
        }
        else if (op == JSP_OPERATOR_ASSIGN_MOD)
        {
          state.operand = dump_prop_setter_or_remainder_res (state.operand, subexpr_state.operand);
        }
        else if (op == JSP_OPERATOR_ASSIGN_ADD)
        {
          state.operand = dump_prop_setter_or_addition_res (state.operand, subexpr_state.operand);
        }
        else if (op == JSP_OPERATOR_ASSIGN_SUB)
        {
          state.operand = dump_prop_setter_or_substraction_res (state.operand, subexpr_state.operand);
        }
        else if (op == JSP_OPERATOR_ASSIGN_LSHIFT)
        {
          state.operand = dump_prop_setter_or_left_shift_res (state.operand, subexpr_state.operand);
        }
        else if (op == JSP_OPERATOR_ASSIGN_RSHIFT)
        {
          state.operand = dump_prop_setter_or_right_shift_res (state.operand, subexpr_state.operand);
        }
        else if (op == JSP_OPERATOR_ASSIGN_RSHIFT_U)
        {
          state.operand = dump_prop_setter_or_right_shift_ex_res (state.operand, subexpr_state.operand);
        }
        else if (op == JSP_OPERATOR_ASSIGN_B_AND)
        {
          state.operand = dump_prop_setter_or_bitwise_and_res (state.operand, subexpr_state.operand);
        }
        else if (op == JSP_OPERATOR_ASSIGN_B_XOR)
        {
          state.operand = dump_prop_setter_or_bitwise_xor_res (state.operand, subexpr_state.operand);
        }
        else
        {
          JERRY_ASSERT (op == JSP_OPERATOR_ASSIGN_B_OR);

          state.operand = dump_prop_setter_or_bitwise_or_res (state.operand, subexpr_state.operand);
        }

        jsp_state_push (state);
      }
      else
      {
        JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0);
        JERRY_ASSERT (state.op == JSP_OPERATOR_NO_OP);

        if (token_is (TOK_DOUBLE_PLUS)
            && !lexer_is_preceded_by_newlines (tok))
        {
          jsp_early_error_check_for_eval_and_arguments_in_strict_mode (state.operand, is_strict_mode (), tok.loc);
          state.operand = dump_post_increment_res (state.operand);

          state.state = JSP_STATE_EXPR_POSTFIX;
          JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0);

          jsp_state_push (state);

          skip_token ();
        }
        else if (token_is (TOK_DOUBLE_MINUS)
                 && !lexer_is_preceded_by_newlines (tok))
        {
          jsp_early_error_check_for_eval_and_arguments_in_strict_mode (state.operand, is_strict_mode (), tok.loc);
          state.operand = dump_post_decrement_res (state.operand);

          state.state = JSP_STATE_EXPR_POSTFIX;
          JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0);

          jsp_state_push (state);

          skip_token ();
        }
        else
        {
          token_type tt = lexer_get_token_type (tok);

          if (tt == TOK_EQ
              || tt == TOK_MULT_EQ
              || tt == TOK_DIV_EQ
              || tt == TOK_MOD_EQ
              || tt == TOK_PLUS_EQ
              || tt == TOK_MINUS_EQ
              || tt == TOK_LSHIFT_EQ
              || tt == TOK_RSHIFT_EQ
              || tt == TOK_RSHIFT_EX_EQ
              || tt == TOK_AND_EQ
              || tt == TOK_XOR_EQ
              || tt == TOK_OR_EQ)
          {
            jsp_early_error_check_for_eval_and_arguments_in_strict_mode (state.operand, is_strict_mode (), tok.loc);

            /* skip the operator */
            skip_token ();

            if (tt == TOK_EQ)
            {
              state.op = JSP_OPERATOR_ASSIGN;
            }
            else if (tt == TOK_MULT_EQ)
            {
              state.op = JSP_OPERATOR_ASSIGN_MUL;
            }
            else if (tt == TOK_DIV_EQ)
            {
              state.op = JSP_OPERATOR_ASSIGN_DIV;
            }
            else if (tt == TOK_MOD_EQ)
            {
              state.op = JSP_OPERATOR_ASSIGN_MOD;
            }
            else if (tt == TOK_PLUS_EQ)
            {
              state.op = JSP_OPERATOR_ASSIGN_ADD;
            }
            else if (tt == TOK_MINUS_EQ)
            {
              state.op = JSP_OPERATOR_ASSIGN_SUB;
            }
            else if (tt == TOK_LSHIFT_EQ)
            {
              state.op = JSP_OPERATOR_ASSIGN_LSHIFT;
            }
            else if (tt == TOK_RSHIFT_EQ)
            {
              state.op = JSP_OPERATOR_ASSIGN_RSHIFT;
            }
            else if (tt == TOK_RSHIFT_EX_EQ)
            {
              state.op = JSP_OPERATOR_ASSIGN_RSHIFT_U;
            }
            else if (tt == TOK_AND_EQ)
            {
              state.op = JSP_OPERATOR_ASSIGN_B_AND;
            }
            else if (tt == TOK_XOR_EQ)
            {
              state.op = JSP_OPERATOR_ASSIGN_B_XOR;
            }
            else
            {
              JERRY_ASSERT (tt == TOK_OR_EQ);

              state.op = JSP_OPERATOR_ASSIGN_B_OR;
            }

            if (state.operand.is_value_based_reference_operand ()
                && !state.operand.is_evaluated_value_based_reference_operand ())
            {
              state.operand = dump_evaluate_if_reference (state.operand);
            }

            jsp_state_push (state);
            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, in_allowed);
          }
          else
          {
            state.state = JSP_STATE_EXPR_POSTFIX;
            JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0);

            jsp_state_push (state);
          }
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_POSTFIX)
    {
      JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0);

      /* propagate to UnaryExpression */
      state.state = JSP_STATE_EXPR_UNARY;

      jsp_state_push (state);
    }
    else if (state.state == JSP_STATE_EXPR_UNARY)
    {
      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        /* propagate to MultiplicativeExpression */
        state.state = JSP_STATE_EXPR_MULTIPLICATIVE;
        state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLETED;

        jsp_state_push (state);
      }
      else
      {
        JERRY_ASSERT (is_subexpr_end);

        if (state.op == JSP_OPERATOR_PREINCR)
        {
          jsp_early_error_check_for_eval_and_arguments_in_strict_mode (subexpr_state.operand, is_strict_mode (), tok.loc);

          state.operand = dump_pre_increment_res (subexpr_state.operand);
        }
        else if (state.op == JSP_OPERATOR_PREDECR)
        {
          jsp_early_error_check_for_eval_and_arguments_in_strict_mode (subexpr_state.operand, is_strict_mode (), tok.loc);

          state.operand = dump_pre_decrement_res (subexpr_state.operand);
        }
        else if (state.op == JSP_OPERATOR_PLUS)
        {
          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);
          state.operand = dump_unary_plus_res (subexpr_state.operand);
        }
        else if (state.op == JSP_OPERATOR_MINUS)
        {
          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);
          state.operand = dump_unary_minus_res (subexpr_state.operand);
        }
        else if (state.op == JSP_OPERATOR_INVERT)
        {
          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);
          state.operand = dump_bitwise_not_res (subexpr_state.operand);
        }
        else if (state.op == JSP_OPERATOR_NOT)
        {
          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);
          state.operand = dump_logical_not_res (subexpr_state.operand);
        }
        else if (state.op == JSP_OPERATOR_DELETE)
        {
          if (subexpr_state.operand.is_identifier_operand ())
          {
            jsp_early_error_check_delete (is_strict_mode (), tok.loc);
          }

          state.operand = dump_delete_res (subexpr_state.operand);
        }
        else if (state.op == JSP_OPERATOR_VOID)
        {
          dump_evaluate_if_reference (subexpr_state.operand);
          state.operand = dump_undefined_assignment_res ();
        }
        else
        {
          JERRY_ASSERT (state.op == JSP_OPERATOR_TYPEOF);

          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);
          state.operand = dump_typeof_res (subexpr_state.operand);
        }

        state.op = JSP_OPERATOR_NO_OP;
        state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

        jsp_state_push (state);
      }
    }
    else if (state.state == JSP_STATE_EXPR_MULTIPLICATIVE)
    {
      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        /* propagate to AdditiveExpression */
        state.state = JSP_STATE_EXPR_ADDITIVE;
        state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLETED;

        jsp_state_push (state);
      }
      else
      {
        if (is_subexpr_end)
        {
          state.operand = dump_assignment_of_lhs_if_value_based_reference (state.operand);
          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);

          if (state.op == JSP_OPERATOR_MUL)
          {
            dump_multiplication (state.operand, state.operand, subexpr_state.operand);
          }
          else if (state.op == JSP_OPERATOR_DIV)
          {
            dump_division (state.operand, state.operand, subexpr_state.operand);
          }
          else
          {
            JERRY_ASSERT (state.op == JSP_OPERATOR_MOD);

            dump_remainder (state.operand, state.operand, subexpr_state.operand);
          }

          state.op = JSP_OPERATOR_NO_OP;

          jsp_state_push (state);
        }
        else if (token_is (TOK_MULT))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_MUL;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_UNARY, in_allowed);
        }
        else if (token_is (TOK_DIV))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_DIV;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_UNARY, in_allowed);
        }
        else if (token_is (TOK_MOD))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_MOD;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_UNARY, in_allowed);
        }
        else
        {
          state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

          jsp_state_push (state);
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_ADDITIVE)
    {
      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        /* propagate to ShiftExpression */
        state.state = JSP_STATE_EXPR_SHIFT;
        state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLETED;

        jsp_state_push (state);
      }
      else
      {
        if (is_subexpr_end)
        {
          state.operand = dump_assignment_of_lhs_if_value_based_reference (state.operand);
          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);

          if (state.op == JSP_OPERATOR_ADD)
          {
            dump_addition (state.operand, state.operand, subexpr_state.operand);
          }
          else
          {
            JERRY_ASSERT (state.op == JSP_OPERATOR_SUB);

            dump_substraction (state.operand, state.operand, subexpr_state.operand);
          }

          state.op = JSP_OPERATOR_NO_OP;

          jsp_state_push (state);
        }
        else if (token_is (TOK_PLUS))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_ADD;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_MULTIPLICATIVE, in_allowed);
        }
        else if (token_is (TOK_MINUS))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_SUB;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_MULTIPLICATIVE, in_allowed);
        }
        else
        {
          state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

          jsp_state_push (state);
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_SHIFT)
    {
      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        /* propagate to RelationalExpression */
        state.state = JSP_STATE_EXPR_RELATIONAL;
        state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLETED;

        jsp_state_push (state);
      }
      else
      {
        if (is_subexpr_end)
        {
          state.operand = dump_assignment_of_lhs_if_value_based_reference (state.operand);
          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);

          if (state.op == JSP_OPERATOR_LSHIFT)
          {
            dump_left_shift (state.operand, state.operand, subexpr_state.operand);
          }
          else if (state.op == JSP_OPERATOR_RSHIFT)
          {
            dump_right_shift (state.operand, state.operand, subexpr_state.operand);
          }
          else
          {
            JERRY_ASSERT (state.op == JSP_OPERATOR_RSHIFT_U);

            dump_right_shift_ex (state.operand, state.operand, subexpr_state.operand);
          }

          state.op = JSP_OPERATOR_NO_OP;

          jsp_state_push (state);
        }
        else if (token_is (TOK_LSHIFT))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_LSHIFT;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ADDITIVE, in_allowed);
        }
        else if (token_is (TOK_RSHIFT))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_RSHIFT;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ADDITIVE, in_allowed);
        }
        else if (token_is (TOK_RSHIFT_EX))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_RSHIFT_U;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ADDITIVE, in_allowed);
        }
        else
        {
          state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

          jsp_state_push (state);
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_RELATIONAL)
    {
      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        /* propagate to EqualityExpression */
        state.state = JSP_STATE_EXPR_EQUALITY;
        state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLETED;

        jsp_state_push (state);
      }
      else
      {
        if (is_subexpr_end)
        {
          state.operand = dump_assignment_of_lhs_if_value_based_reference (state.operand);
          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);

          if (state.op == JSP_OPERATOR_LESS)
          {
            dump_less_than (state.operand, state.operand, subexpr_state.operand);
          }
          else if (state.op == JSP_OPERATOR_GREATER)
          {
            dump_greater_than (state.operand, state.operand, subexpr_state.operand);
          }
          else if (state.op == JSP_OPERATOR_LESS_OR_EQUAL)
          {
            dump_less_or_equal_than (state.operand, state.operand, subexpr_state.operand);
          }
          else if (state.op == JSP_OPERATOR_GREATER_OR_EQUAL)
          {
            dump_greater_or_equal_than (state.operand, state.operand, subexpr_state.operand);
          }
          else if (state.op == JSP_OPERATOR_INSTANCEOF)
          {
            dump_instanceof (state.operand, state.operand, subexpr_state.operand);
          }
          else
          {
            JERRY_ASSERT (state.op == JSP_OPERATOR_IN);
            JERRY_ASSERT (in_allowed);

            dump_in (state.operand, state.operand, subexpr_state.operand);
          }

          state.op = JSP_OPERATOR_NO_OP;

          jsp_state_push (state);
        }
        else if (token_is (TOK_LESS))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_LESS;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_SHIFT, in_allowed);
        }
        else if (token_is (TOK_GREATER))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_GREATER;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_SHIFT, in_allowed);
        }
        else if (token_is (TOK_LESS_EQ))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_LESS_OR_EQUAL;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_SHIFT, in_allowed);
        }
        else if (token_is (TOK_GREATER_EQ))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_GREATER_OR_EQUAL;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_SHIFT, in_allowed);
        }
        else if (token_is (TOK_KEYWORD) && is_keyword (KW_INSTANCEOF))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_INSTANCEOF;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_SHIFT, in_allowed);
        }
        else if (in_allowed && token_is (TOK_KEYWORD) && is_keyword (KW_IN))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_IN;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_SHIFT, in_allowed);
        }
        else
        {
          state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

          jsp_state_push (state);
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_EQUALITY)
    {
      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        /* propagate to BitwiseAndExpression */
        state.state = JSP_STATE_EXPR_BITWISE_AND;
        state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLETED;

        jsp_state_push (state);
      }
      else
      {
        if (is_subexpr_end)
        {
          state.operand = dump_assignment_of_lhs_if_value_based_reference (state.operand);
          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);

          if (state.op == JSP_OPERATOR_EQUAL)
          {
            dump_equal_value (state.operand, state.operand, subexpr_state.operand);
          }
          else if (state.op == JSP_OPERATOR_NOT_EQUAL)
          {
            dump_not_equal_value (state.operand, state.operand, subexpr_state.operand);
          }
          else if (state.op == JSP_OPERATOR_STRICT_EQUAL)
          {
            dump_equal_value_type (state.operand, state.operand, subexpr_state.operand);
          }
          else
          {
            JERRY_ASSERT (state.op == JSP_OPERATOR_STRICT_NOT_EQUAL);

            dump_not_equal_value_type (state.operand, state.operand, subexpr_state.operand);
          }

          state.op = JSP_OPERATOR_NO_OP;

          jsp_state_push (state);
        }
        else if (token_is (TOK_DOUBLE_EQ))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_EQUAL;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_RELATIONAL, in_allowed);
        }
        else if (token_is (TOK_NOT_EQ))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_NOT_EQUAL;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_RELATIONAL, in_allowed);
        }
        else if (token_is (TOK_TRIPLE_EQ))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_STRICT_EQUAL;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_RELATIONAL, in_allowed);
        }
        else if (token_is (TOK_NOT_DOUBLE_EQ))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_STRICT_NOT_EQUAL;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_RELATIONAL, in_allowed);
        }
        else
        {
          state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

          jsp_state_push (state);
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_BITWISE_AND)
    {
      /* FIXME: Consider merging BitwiseOR / BitwiseXOR / BitwiseAND productions
       * into one production with different operators, taking their precedence into account */

      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        /* propagate to BitwiseXorExpression */
        state.state = JSP_STATE_EXPR_BITWISE_XOR;
        state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLETED;

        jsp_state_push (state);
      }
      else
      {
        if (is_subexpr_end)
        {
          state.operand = dump_assignment_of_lhs_if_value_based_reference (state.operand);
          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);

          JERRY_ASSERT (state.op == JSP_OPERATOR_B_AND);

          state.op = JSP_OPERATOR_NO_OP;
          dump_bitwise_and (state.operand, state.operand, subexpr_state.operand);

          jsp_state_push (state);
        }
        else if (token_is (TOK_AND))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_B_AND;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_EQUALITY, in_allowed);
        }
        else
        {
          state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

          jsp_state_push (state);
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_BITWISE_XOR)
    {
      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        /* propagate to BitwiseOrExpression */
        state.state = JSP_STATE_EXPR_BITWISE_OR;
        state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLETED;

        jsp_state_push (state);
      }
      else
      {
        if (is_subexpr_end)
        {
          state.operand = dump_assignment_of_lhs_if_value_based_reference (state.operand);
          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);

          JERRY_ASSERT (state.op == JSP_OPERATOR_B_XOR);

          state.op = JSP_OPERATOR_NO_OP;
          dump_bitwise_xor (state.operand, state.operand, subexpr_state.operand);

          jsp_state_push (state);
        }
        else if (token_is (TOK_XOR))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_B_XOR;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_BITWISE_AND, in_allowed);
        }
        else
        {
          state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

          jsp_state_push (state);
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_BITWISE_OR)
    {
      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        /* propagate to LogicalAndExpression */
        state.state = JSP_STATE_EXPR_LOGICAL_AND;
        state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLETED;

        jsp_state_push (state);
      }
      else
      {
        if (is_subexpr_end)
        {
          state.operand = dump_assignment_of_lhs_if_value_based_reference (state.operand);
          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);

          JERRY_ASSERT (state.op == JSP_OPERATOR_B_OR);

          state.op = JSP_OPERATOR_NO_OP;
          dump_bitwise_or (state.operand, state.operand, subexpr_state.operand);

          jsp_state_push (state);
        }
        else if (token_is (TOK_OR))
        {
          skip_token ();

          state.operand = dump_assignment_of_lhs_if_reference (state.operand);
          state.op = JSP_OPERATOR_B_OR;

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_BITWISE_XOR, in_allowed);
        }
        else
        {
          state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

          jsp_state_push (state);
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_LOGICAL_AND)
    {
      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        /* propagate to LogicalOrExpression */
        state.state = JSP_STATE_EXPR_LOGICAL_OR;
        state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLETED;

        jsp_state_push (state);
      }
      else
      {
        if (is_subexpr_end)
        {
          state.operand = dump_assignment_of_lhs_if_value_based_reference (state.operand);
          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);

          JERRY_ASSERT (state.op == JSP_OPERATOR_LOGICAL_AND);

          JERRY_ASSERT (state.operand.is_register_operand ());

          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);

          dump_variable_assignment (state.operand, subexpr_state.operand);

          state.op = JSP_OPERATOR_NO_OP;

          jsp_state_push (state);
        }
        else
        {
          JERRY_ASSERT (state.op == JSP_OPERATOR_NO_OP);

          if (token_is (TOK_DOUBLE_AND))
          {
            /* ECMA-262 v5, 11.11 (complex LogicalAndExpression) */
            skip_token ();

            /*
             * FIXME:
             *       Consider eliminating COMPLEX_PRODUCTION flag through implementing rewrite chain
             */

            if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLEX_PRODUCTION) == 0)
            {
              state.flags |= JSP_STATE_EXPR_FLAG_COMPLEX_PRODUCTION;

              JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_FIXED_RET_OPERAND) == 0);

              jsp_operand_t ret = tmp_operand ();

              state.operand = dump_assignment_of_lhs_if_value_based_reference (state.operand);
              dump_variable_assignment (ret, state.operand);

              start_dumping_logical_and_checks ();

              state.flags |= JSP_STATE_EXPR_FLAG_FIXED_RET_OPERAND;
              state.operand = ret;
            }

            JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_COMPLEX_PRODUCTION) != 0);

            dump_logical_and_check_for_rewrite (state.operand);

            state.op = JSP_OPERATOR_LOGICAL_AND;

            jsp_state_push (state);
            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_BITWISE_OR, in_allowed);
          }
          else
          {
            /* end of LogicalAndExpression */
            JERRY_ASSERT (state.op == JSP_OPERATOR_NO_OP);

            if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLEX_PRODUCTION) != 0)
            {
              rewrite_logical_and_checks ();

              state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLEX_PRODUCTION;
            }

            state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

            jsp_state_push (state);
          }
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_LOGICAL_OR)
    {
      if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0)
      {
        /* switching to ConditionalExpression */
        state.state = JSP_STATE_EXPR_CONDITION;

        if (token_is (TOK_QUERY))
        {
          state.state = JSP_STATE_EXPR_CONDITION;
          state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLETED;

          /* ECMA-262 v5, 11.12 */
          skip_token ();

          dump_conditional_check_for_rewrite (state.operand);

          state.op = JSP_OPERATOR_QUERY;

          JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_FIXED_RET_OPERAND) == 0);

          state.flags |= JSP_STATE_EXPR_FLAG_FIXED_RET_OPERAND;
          state.operand = tmp_operand ();

          jsp_state_push (state);
          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, true);
        }
        else
        {
          /* just propagate */
          jsp_state_push (state);
        }
      }
      else
      {
        if (is_subexpr_end)
        {
          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);

          JERRY_ASSERT (state.op == JSP_OPERATOR_LOGICAL_OR);

          JERRY_ASSERT (state.operand.is_register_operand ());
          dump_variable_assignment (state.operand, subexpr_state.operand);

          state.op = JSP_OPERATOR_NO_OP;

          jsp_state_push (state);
        }
        else
        {
          JERRY_ASSERT (state.op == JSP_OPERATOR_NO_OP);

          if (token_is (TOK_DOUBLE_OR))
          {
            /* ECMA-262 v5, 11.11 (complex LogicalOrExpression) */
            skip_token ();

            /*
             * FIXME:
             *       Consider eliminating COMPLEX_PRODUCTION flag through implementing rewrite chain
             */

            if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLEX_PRODUCTION) == 0)
            {
              state.flags |= JSP_STATE_EXPR_FLAG_COMPLEX_PRODUCTION;

              JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_FIXED_RET_OPERAND) == 0);

              jsp_operand_t ret = tmp_operand ();

              state.operand = dump_assignment_of_lhs_if_value_based_reference (state.operand);
              dump_variable_assignment (ret, state.operand);

              start_dumping_logical_or_checks ();

              state.flags |= JSP_STATE_EXPR_FLAG_FIXED_RET_OPERAND;
              state.operand = ret;
            }

            JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_COMPLEX_PRODUCTION) != 0);

            dump_logical_or_check_for_rewrite (state.operand);

            state.op = JSP_OPERATOR_LOGICAL_OR;

            jsp_state_push (state);
            jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_LOGICAL_AND, in_allowed);
          }
          else
          {
            /* end of LogicalOrExpression */
            JERRY_ASSERT (state.op == JSP_OPERATOR_NO_OP);

            if ((state.flags & JSP_STATE_EXPR_FLAG_COMPLEX_PRODUCTION) != 0)
            {
              rewrite_logical_or_checks ();

              state.flags &= ~JSP_STATE_EXPR_FLAG_COMPLEX_PRODUCTION;
            }

            state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

            jsp_state_push (state);
          }
        }
      }
    }
    else if (state.state == JSP_STATE_EXPR_ASSIGNMENT)
    {
      /* assignment production can't be continued at the point */
      JERRY_ASSERT (!is_subexpr_end);

      JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0);
      JERRY_ASSERT (state.op == JSP_OPERATOR_NO_OP);

      /* 'assignment expression' production can't be continued with an operator,
       *  so just propagating it to 'expression' production */
      state.flags &= ~(JSP_STATE_EXPR_FLAG_COMPLETED);
      state.state = JSP_STATE_EXPR_EXPRESSION;

      jsp_state_push (state);
    }
    else if (state.state == JSP_STATE_EXPR_CONDITION)
    {
      /* ECMA-262 v5, 11.12 */
      if (is_subexpr_end)
      {
        if (state.op == JSP_OPERATOR_QUERY)
        {
          current_token_must_be (TOK_COLON);
          skip_token ();

          JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_FIXED_RET_OPERAND) != 0);
          JERRY_ASSERT (state.operand.is_register_operand ());
          JERRY_ASSERT (subexpr_state.state == JSP_STATE_EXPR_ASSIGNMENT);

          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);

          dump_variable_assignment (state.operand, subexpr_state.operand);

          dump_jump_to_end_for_rewrite ();
          rewrite_conditional_check ();

          state.op = JSP_OPERATOR_COLON;

          jsp_state_push (state);

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, in_allowed);
        }
        else
        {
          JERRY_ASSERT (state.op == JSP_OPERATOR_COLON);

          JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_FIXED_RET_OPERAND) != 0);
          JERRY_ASSERT (state.operand.is_register_operand ());
          JERRY_ASSERT (subexpr_state.state == JSP_STATE_EXPR_ASSIGNMENT);

          subexpr_state.operand = dump_assignment_of_lhs_if_value_based_reference (subexpr_state.operand);

          dump_variable_assignment (state.operand, subexpr_state.operand);
          rewrite_jump_to_end ();

          state.op = JSP_OPERATOR_NO_OP;
          state.flags &= ~JSP_STATE_EXPR_FLAG_FIXED_RET_OPERAND;
          state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

          jsp_state_push (state);
        }
      }
      else
      {
        /* ConditionalExpression is finished, so can't contain more subexpressions,
         * so just propagate it to AssignmentExpression */
        JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0);

        state.state = JSP_STATE_EXPR_ASSIGNMENT;

        jsp_state_push (state);
      }
    }
    else if (state.state == JSP_STATE_EXPR_EXPRESSION)
    {
      /* ECMA-262 v5, 11.14 */

      if (is_subexpr_end)
      {
        JERRY_ASSERT (state.op == JSP_OPERATOR_COMMA);

        /*
         * The operand should be already evaluated
         *
         * See also:
         *          11.14, step 2
         */
        JERRY_ASSERT (state.operand.is_register_operand ());

        if (!subexpr_state.operand.is_register_operand ())
        {
          /* evaluating, if reference */
          subexpr_state.operand = dump_assignment_of_lhs_if_reference (subexpr_state.operand);
        }

        state.operand = subexpr_state.operand;

        jsp_state_push (state);
      }
      else
      {
        JERRY_ASSERT ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) == 0);

        if (token_is (TOK_COMMA))
        {
          skip_token ();

          JERRY_ASSERT (!token_is (TOK_COMMA));

          state.op = JSP_OPERATOR_COMMA;

          /* ECMA-262 v5, 11.14, step 2 */
          state.operand = dump_assignment_of_lhs_if_reference (state.operand);

          jsp_state_push (state);

          jsp_push_new_expr_state (JSP_STATE_EXPR_EMPTY, JSP_STATE_EXPR_ASSIGNMENT, in_allowed);
        }
        else
        {
          state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;

          jsp_state_push (state);
        }
      }
    }
    else
    {
      JERRY_UNIMPLEMENTED ("Parse of the expression type is not currently implemented");
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
  else
  {
    lexer_save_token (tok);
  }

  return name;
} /* parse_variable_declaration */

/* variable_declaration_list
  : variable_declaration
    (LT!* ',' LT!* variable_declaration)*
  ; */
static void
parse_variable_declaration_list (void)
{
  JERRY_ASSERT (is_keyword (KW_VAR));

  while (true)
  {
    skip_token ();

    parse_variable_declaration ();

    skip_token ();
    if (!token_is (TOK_COMMA))
    {
      lexer_save_token (tok);
      break;
    }
  }
}

/**
 * Parse for statement
 *
 * See also:
 *          ECMA-262 v5, 12.6.3
 *
 * Note:
 *      Syntax:
 *               Initializer                      Condition     Increment     Body      LoopEnd
 *       - for ([ExpressionNoIn];                [Expression]; [Expression]) Statement
 *       - for (var VariableDeclarationListNoIn; [Expression]; [Expression]) Statement
 *
 * Note:
 *      Layout of generated byte-code is the following:
 *                        Initializer ([ExpressionNoIn] / VariableDeclarationListNoIn)
 *                        Jump -> ConditionCheck
 *        NextIteration:
 *                        Body (Statement)
 *        ContinueTarget:
 *                        Increment ([Expression])
 *        ConditionCheck:
 *                        Condition ([Expression])
 *                        If Condition is evaluted to true, jump -> NextIteration
 */
static void
jsp_parse_for_statement (jsp_label_t *outermost_stmt_label_p, /**< outermost (first) label, corresponding to
                                                               *   the statement (or NULL, if there are no named
                                                               *   labels associated with the statement) */
                         locus for_body_statement_loc) /**< locus of loop body statement */
{
  current_token_must_be (TOK_OPEN_PAREN);
  skip_token ();

  // Initializer
  if (is_keyword (KW_VAR))
  {
    parse_variable_declaration_list ();
    skip_token ();
  }
  else if (!token_is (TOK_SEMICOLON))
  {
    parse_expression (false, JSP_EVAL_RET_STORE_NOT_DUMP);
    skip_token ();
  }
  else
  {
    // Initializer is empty
  }

  // Jump -> ConditionCheck
  dump_jump_to_end_for_rewrite ();

  dumper_set_next_interation_target ();

  current_token_must_be (TOK_SEMICOLON);
  skip_token ();

  // Save Condition locus
  const locus condition_loc = tok.loc;

  if (!jsp_find_next_token_before_the_locus (TOK_SEMICOLON,
                                             for_body_statement_loc,
                                             true))
  {
    EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Invalid for statement");
  }

  current_token_must_be (TOK_SEMICOLON);
  skip_token ();

  // Save Increment locus
  const locus increment_loc = tok.loc;

  // Body
  lexer_seek (for_body_statement_loc);
  skip_token ();

  parse_statement (NULL);

  // Save LoopEnd locus
  const locus loop_end_loc = tok.loc;

  // Setup ContinueTarget
  jsp_label_setup_continue_target (outermost_stmt_label_p,
                                   serializer_get_current_instr_counter ());

  // Increment
  lexer_seek (increment_loc);
  skip_token ();

  if (!token_is (TOK_CLOSE_PAREN))
  {
    parse_expression (true, JSP_EVAL_RET_STORE_NOT_DUMP);
  }

  current_token_must_be (TOK_CLOSE_PAREN);

  // Setup ConditionCheck
  rewrite_jump_to_end ();

  // Condition
  lexer_seek (condition_loc);
  skip_token ();

  if (token_is (TOK_SEMICOLON))
  {
    dump_continue_iterations_check (empty_operand ());
  }
  else
  {
    jsp_operand_t cond = parse_expression (true, JSP_EVAL_RET_STORE_NOT_DUMP);
    dump_continue_iterations_check (cond);
  }

  lexer_seek (loop_end_loc);
  skip_token ();
  if (lexer_get_token_type (tok) != TOK_CLOSE_BRACE)
  {
    lexer_save_token (tok);
  }
} /* jsp_parse_for_statement */

/**
 * Parse VariableDeclarationNoIn / LeftHandSideExpression (iterator part) of for-in statement
 *
 * See also:
 *          jsp_parse_for_in_statement
 *
 * @return operand - result of iterator expression evaluation
 */
static jsp_operand_t
jsp_parse_for_in_statement_iterator (void)
{
  if (is_keyword (KW_VAR))
  {
    skip_token ();

    jsp_operand_t name = parse_variable_declaration ();
    JERRY_ASSERT (name.is_literal_operand ());

    return jsp_operand_t::make_identifier_operand (name.get_literal ());
  }
  else
  {
    return parse_expression_ (JSP_STATE_EXPR_LEFTHANDSIDE, true);
  }
} /* jsp_parse_for_in_statement_iterator */

/**
 * Parse for-in statement
 *
 * See also:
 *          ECMA-262 v5, 12.6.4
 *
 * Note:
 *      Syntax:
 *                     Iterator                 Collection   Body     LoopEnd
 *       - for (    LeftHandSideExpression  in Expression) Statement
 *       - for (var VariableDeclarationNoIn in Expression) Statement
 *
 * Note:
 *      Layout of generate byte-code is the following:
 *                        tmp <- Collection (Expression)
 *                        for_in instruction (tmp, instruction counter of for-in end mark)
 *                         {
 *                          Assignment of VM_REG_SPECIAL_FOR_IN_PROPERTY_NAME to
 *                          Iterator (VariableDeclarationNoIn / LeftHandSideExpression)
 *                         }
 *                         Body (Statement)
 *        ContinueTarget:
 *                        meta (OPCODE_META_TYPE_END_FOR_IN)
 */
static void
jsp_parse_for_in_statement (jsp_label_t *outermost_stmt_label_p, /**< outermost (first) label,
                                                                  *   corresponding to the statement
                                                                  *   (or NULL, if there are no name
                                                                  *   labels associated with the statement) */
                            locus for_body_statement_loc) /**< locus of loop body statement */
{
  bool is_raised = jsp_label_raise_nested_jumpable_border ();

  current_token_must_be (TOK_OPEN_PAREN);
  skip_token ();

  // Save Iterator location
  locus iterator_loc = tok.loc;

  while (lit_utf8_iterator_pos_cmp (tok.loc, for_body_statement_loc) < 0)
  {
    if (jsp_find_next_token_before_the_locus (TOK_KEYWORD,
                                              for_body_statement_loc,
                                              true))
    {
      if (is_keyword (KW_IN))
      {
        break;
      }
      else
      {
        skip_token ();
      }
    }
    else
    {
      EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Invalid for statement");
    }
  }

  JERRY_ASSERT (is_keyword (KW_IN));
  skip_token ();

  // Collection
  jsp_operand_t collection = parse_expression (true, JSP_EVAL_RET_STORE_NOT_DUMP);
  current_token_must_be (TOK_CLOSE_PAREN);
  skip_token ();

  // Dump for-in instruction
  collection = dump_assignment_of_lhs_if_value_based_reference (collection);
  vm_instr_counter_t for_in_oc = dump_for_in_for_rewrite (collection);

  // Dump assignment VariableDeclarationNoIn / LeftHandSideExpression <- VM_REG_SPECIAL_FOR_IN_PROPERTY_NAME
  lexer_seek (iterator_loc);
  tok = lexer_next_token (false);

  jsp_operand_t iterator, for_in_special_reg;
  for_in_special_reg = jsp_create_operand_for_in_special_reg ();

  iterator = jsp_parse_for_in_statement_iterator ();

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

  parse_statement (NULL);

  // Save LoopEnd locus
  const locus loop_end_loc = tok.loc;

  // Setup ContinueTarget
  jsp_label_setup_continue_target (outermost_stmt_label_p,
                                   serializer_get_current_instr_counter ());

  // Write position of for-in end to for_in instruction
  rewrite_for_in (for_in_oc);

  // Dump meta (OPCODE_META_TYPE_END_FOR_IN)
  dump_for_in_end ();

  lexer_seek (loop_end_loc);
  tok = lexer_next_token (false);
  if (lexer_get_token_type (tok) != TOK_CLOSE_BRACE)
  {
    lexer_save_token (tok);
  }

  if (is_raised)
  {
    jsp_label_remove_nested_jumpable_border ();
  }
} /* jsp_parse_for_in_statement */

/**
 * Parse for/for-in statements
 *
 * See also:
 *          ECMA-262 v5, 12.6.3 and 12.6.4
 */
static void
jsp_parse_for_or_for_in_statement (jsp_label_t *outermost_stmt_label_p) /**< outermost (first) label,
                                                                         *   corresponding to the statement
                                                                         *   (or NULL, if there are no name
                                                                         *   labels associated with the statement) */
{
  assert_keyword (KW_FOR);

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

  if (is_plain_for)
  {
    jsp_parse_for_statement (outermost_stmt_label_p, for_body_statement_loc);
  }
  else
  {
    jsp_parse_for_in_statement (outermost_stmt_label_p, for_body_statement_loc);
  }
} /* jsp_parse_for_or_for_in_statement */

static jsp_operand_t
parse_expression_inside_parens (void)
{
  skip_token ();
  current_token_must_be (TOK_OPEN_PAREN);
  skip_token ();

  const jsp_operand_t res = parse_expression (true, JSP_EVAL_RET_STORE_NOT_DUMP);

  skip_token ();
  current_token_must_be (TOK_CLOSE_PAREN);

  return res;
}

static void
jsp_start_statement_parse (jsp_state_expr_t req_stat)
{
  jsp_state_t new_state;

  new_state.state = JSP_STATE_EXPR_EMPTY;
  new_state.req_expr_type = req_stat;
  new_state.operand = empty_operand ();
  new_state.op = JSP_OPERATOR_NO_OP;
  new_state.rewrite_chain = MAX_OPCODES; /* empty chain */
  new_state.flags = JSP_STATE_EXPR_FLAG_NO_FLAGS;

  jsp_state_push (new_state);
} /* jsp_start_statement_parse */

static void
insert_semicolon (void)
{
  // We cannot use tok, since we may use lexer_save_token
  skip_token ();

  bool is_new_line_occured = lexer_is_preceded_by_newlines (tok);
  bool is_close_brace_or_eof = (token_is (TOK_CLOSE_BRACE) || token_is (TOK_EOF));

  if (is_new_line_occured || is_close_brace_or_eof)
  {
    lexer_save_token (tok);
  }
  else if (!token_is (TOK_SEMICOLON) && !token_is (TOK_EOF))
  {
    EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Expected either ';' or newline token");
  }
}

/**
 * Parse statement
 */
static void
parse_statement_ (void)
{
  uint32_t start_pos = jsp_state_stack_pos;

  jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT);

  while (true)
  {
    jsp_state_t state, subexpr_state;

    state = jsp_state_top ();
    jsp_state_pop ();

    if (state.state == state.req_expr_type
        && ((state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0))
    {
      (void) jsp_is_stack_empty ();

      if (start_pos == jsp_state_stack_pos) // FIXME: jsp_is_stack_empty ()
      {
        break;
      }
      else
      {
        subexpr_state = state;

        state = jsp_state_top ();
        jsp_state_pop ();

        JERRY_ASSERT ((subexpr_state.flags & JSP_STATE_EXPR_FLAG_COMPLETED) != 0);
      }
    }

    if (state.state == JSP_STATE_EXPR_EMPTY)
    {
      if (is_keyword (KW_IF)) /* IfStatement */
      {
        jsp_operand_t cond = parse_expression_inside_parens ();
        cond = dump_assignment_of_lhs_if_value_based_reference (cond);
        dump_conditional_check_for_rewrite (cond);

        skip_token ();

        state.state = JSP_STATE_STAT_IF_BRANCH_START;
        jsp_state_push (state);
        jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT);
      }
      else if (token_is (TOK_OPEN_BRACE))
      {
        skip_token ();
        if (!token_is (TOK_CLOSE_BRACE))
        {
          state.state = JSP_STATE_STAT_STATEMENT_LIST;
          jsp_state_push (state);
          jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT);
        }
        else
        {
          state.state = JSP_STATE_STAT_STATEMENT;
          state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;
          jsp_state_push (state);
        }
      }
      else if (is_keyword (KW_VAR))
      {
        state.state = JSP_STATE_STAT_VAR_DECL;
        jsp_state_push (state);
      }
      else
      {
        parse_statement (NULL);

        state.state = JSP_STATE_STAT_STATEMENT;
        state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;
        jsp_state_push (state);
      }
    }
    else if (state.state == JSP_STATE_STAT_IF_BRANCH_START)
    {
      skip_token ();
      if (is_keyword (KW_ELSE))
      {
        dump_jump_to_end_for_rewrite ();
        rewrite_conditional_check ();

        skip_token ();
        state.state = JSP_STATE_STAT_IF_BRANCH_END;
        jsp_state_push (state);
        jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT);
      }
      else
      {
        lexer_save_token (tok);
        rewrite_conditional_check ();

        state.state = JSP_STATE_STAT_STATEMENT;
        state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;
        jsp_state_push (state);
      }
    }
    else if (state.state == JSP_STATE_STAT_IF_BRANCH_END)
    {
      rewrite_jump_to_end ();

      state.state = JSP_STATE_STAT_STATEMENT;
      state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;
      jsp_state_push (state);
    }
    else if (state.state == JSP_STATE_STAT_STATEMENT_LIST)
    {
      skip_token ();
      while (token_is (TOK_SEMICOLON))
      {
        skip_token ();
      }

      if (token_is (TOK_CLOSE_BRACE)
          || (is_keyword (KW_CASE) || is_keyword (KW_DEFAULT)))
      {
        //lexer_save_token (tok);

        state.state = JSP_STATE_STAT_STATEMENT;
        state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;
        jsp_state_push (state);
      }
      else
      {
        jsp_state_push (state);
        jsp_start_statement_parse (JSP_STATE_STAT_STATEMENT);
      }
    }
    else if (state.state == JSP_STATE_STAT_VAR_DECL)
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
      else
      {
        lexer_save_token (tok);
      }

      skip_token ();

      if (!token_is (TOK_COMMA))
      {
        lexer_save_token (tok);

        if (token_is (TOK_SEMICOLON))
        {
          skip_token ();
        }
        else
        {
          insert_semicolon ();
        }

        state.state = JSP_STATE_STAT_STATEMENT;
        state.flags |= JSP_STATE_EXPR_FLAG_COMPLETED;
        jsp_state_push (state);
      }
      else
      {
        jsp_state_push (state);
      }
    }
  }
} /* parse_statement_ */

/* statement_list
  : statement (LT!* statement)*
  ; */
static void
parse_statement_list (void)
{
  while (true)
  {
    parse_statement (NULL);

    skip_token ();
    while (token_is (TOK_SEMICOLON))
    {
      skip_token ();
    }
    if (token_is (TOK_CLOSE_BRACE))
    {
      lexer_save_token (tok);
      break;
    }
    if (is_keyword (KW_CASE) || is_keyword (KW_DEFAULT))
    {
      lexer_save_token (tok);
      break;
    }
  }
}

/* if_statement
  : 'if' LT!* '(' LT!* expression LT!* ')' LT!* statement (LT!* 'else' LT!* statement)?
  ; */
static void
parse_if_statement (void)
{
  assert_keyword (KW_IF);

  jsp_operand_t cond = parse_expression_inside_parens ();
  cond = dump_assignment_of_lhs_if_value_based_reference (cond);
  dump_conditional_check_for_rewrite (cond);

  skip_token ();
  parse_statement (NULL);

  skip_token ();
  if (is_keyword (KW_ELSE))
  {
    dump_jump_to_end_for_rewrite ();
    rewrite_conditional_check ();

    skip_token ();
    parse_statement (NULL);

    rewrite_jump_to_end ();
  }
  else
  {
    lexer_save_token (tok);
    rewrite_conditional_check ();
  }
}

/* do_while_statement
  : 'do' LT!* statement LT!* 'while' LT!* '(' expression ')' (LT | ';')!
  ; */
static void
parse_do_while_statement (jsp_label_t *outermost_stmt_label_p) /**< outermost (first) label, corresponding to
                                                                *   the statement (or NULL, if there are no named
                                                                *   labels associated with the statement) */
{
  assert_keyword (KW_DO);

  dumper_set_next_interation_target ();

  skip_token ();
  parse_statement (NULL);

  jsp_label_setup_continue_target (outermost_stmt_label_p,
                                   serializer_get_current_instr_counter ());

  skip_token ();
  assert_keyword (KW_WHILE);

  const jsp_operand_t cond = parse_expression_inside_parens ();
  dump_continue_iterations_check (cond);
}

/* while_statement
  : 'while' LT!* '(' LT!* expression LT!* ')' LT!* statement
  ; */
static void
parse_while_statement (jsp_label_t *outermost_stmt_label_p) /**< outermost (first) label, corresponding to
                                                             *   the statement (or NULL, if there are no named
                                                             *   labels associated with the statement) */
{
  assert_keyword (KW_WHILE);

  skip_token ();
  current_token_must_be (TOK_OPEN_PAREN);

  const locus cond_loc = tok.loc;
  jsp_skip_braces (TOK_OPEN_PAREN);

  dump_jump_to_end_for_rewrite ();

  dumper_set_next_interation_target ();

  skip_token ();
  parse_statement (NULL);

  jsp_label_setup_continue_target (outermost_stmt_label_p,
                                   serializer_get_current_instr_counter ());

  rewrite_jump_to_end ();

  const locus end_loc = tok.loc;
  lexer_seek (cond_loc);
  const jsp_operand_t cond = parse_expression_inside_parens ();
  dump_continue_iterations_check (cond);

  lexer_seek (end_loc);
  skip_token ();
}

/* with_statement
  : 'with' LT!* '(' LT!* expression LT!* ')' LT!* statement
  ; */
static void
parse_with_statement (void)
{
  assert_keyword (KW_WITH);
  if (is_strict_mode ())
  {
    EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "'with' expression is not allowed in strict mode.");
  }
  const jsp_operand_t expr = parse_expression_inside_parens ();

  scopes_tree_set_contains_with (serializer_get_scope ());

  bool is_raised = jsp_label_raise_nested_jumpable_border ();

  vm_instr_counter_t with_begin_oc = dump_with_for_rewrite (expr);
  skip_token ();
  parse_statement (NULL);
  rewrite_with (with_begin_oc);
  dump_with_end ();

  if (is_raised)
  {
    jsp_label_remove_nested_jumpable_border ();
  }
}

static void
skip_case_clause_body (void)
{
  while (!is_keyword (KW_CASE)
         && !is_keyword (KW_DEFAULT)
         && !token_is (TOK_CLOSE_BRACE))
  {
    if (token_is (TOK_OPEN_BRACE))
    {
      jsp_skip_braces (TOK_OPEN_BRACE);
    }
    skip_token ();
  }
}

/* switch_statement
  : 'switch' LT!* '(' LT!* expression LT!* ')' LT!* '{' LT!* case_block LT!* '}'
  ;
   case_block
  : '{' LT!* case_clause* LT!* '}'
  | '{' LT!* case_clause* LT!* default_clause LT!* case_clause* LT!* '}'
  ;
   case_clause
  : 'case' LT!* expression LT!* ':' LT!* statement*
  ; */
static void
parse_switch_statement (void)
{
  assert_keyword (KW_SWITCH);

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
  while (is_keyword (KW_CASE) || is_keyword (KW_DEFAULT))
  {
    if (is_keyword (KW_CASE))
    {
      skip_token ();
      jsp_operand_t case_expr = parse_expression (true, JSP_EVAL_RET_STORE_NOT_DUMP);
      case_expr = dump_assignment_of_lhs_if_value_based_reference (case_expr);

      skip_token ();
      current_token_must_be (TOK_COLON);

      dump_case_clause_check_for_rewrite (switch_expr, case_expr);
      skip_token ();
      body_locs = array_list_append (body_locs, (void*) &tok.loc);
      skip_case_clause_body ();
    }
    else if (is_keyword (KW_DEFAULT))
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

  jsp_label_t label;
  jsp_label_push (&label,
                  JSP_LABEL_TYPE_UNNAMED_BREAKS,
                  TOKEN_EMPTY_INITIALIZER);

  // Second, parse case clauses' bodies and rewrite jumps
  skip_token ();
  for (size_t i = 0; i < array_list_len (body_locs); i++)
  {
    locus loc = * (locus*) array_list_element (body_locs, i);
    lexer_seek (loc);
    skip_token ();
    if (was_default && default_body_index == i)
    {
      rewrite_default_clause ();
      if (is_keyword (KW_CASE))
      {
        continue;
      }
    }
    else
    {
      rewrite_case_clause ();
      if (is_keyword (KW_CASE) || is_keyword (KW_DEFAULT))
      {
        continue;
      }
    }
    parse_statement_list ();
    skip_token ();
  }

  if (!was_default)
  {
    rewrite_default_clause ();
  }

  current_token_must_be (TOK_CLOSE_BRACE);
  skip_token ();

  jsp_label_rewrite_jumps_and_pop (&label,
                                   serializer_get_current_instr_counter ());

  finish_dumping_case_clauses ();
  array_list_free (body_locs);

  lexer_save_token (tok);
}

/* catch_clause
  : 'catch' LT!* '(' LT!* Identifier LT!* ')' LT!* '{' LT!* statement_list LT!* '}'
  ; */
static void
parse_catch_clause (void)
{
  assert_keyword (KW_CATCH);

  skip_token ();
  current_token_must_be (TOK_OPEN_PAREN);

  skip_token ();
  current_token_must_be (TOK_NAME);

  const jsp_operand_t exception = literal_operand (token_data_as_lit_cp ());
  jsp_early_error_check_for_eval_and_arguments_in_strict_mode (exception, is_strict_mode (), tok.loc);

  skip_token ();
  current_token_must_be (TOK_CLOSE_PAREN);

  dump_catch_for_rewrite (exception);

  skip_token ();
  current_token_must_be (TOK_OPEN_BRACE);
  skip_token ();

  parse_statement_list ();

  skip_token ();
  current_token_must_be (TOK_CLOSE_BRACE);

  rewrite_catch ();
}

/* finally_clause
  : 'finally' LT!* '{' LT!* statement_list LT!* '}'
  ; */
static void
parse_finally_clause (void)
{
  assert_keyword (KW_FINALLY);

  dump_finally_for_rewrite ();

  skip_token ();
  current_token_must_be (TOK_OPEN_BRACE);
  skip_token ();

  parse_statement_list ();

  skip_token ();
  current_token_must_be (TOK_CLOSE_BRACE);

  rewrite_finally ();
}

/* try_statement
  : 'try' LT!* '{' LT!* statement_list LT!* '}' LT!* (finally_clause | catch_clause (LT!* finally_clause)?)
  ; */
static void
parse_try_statement (void)
{
  assert_keyword (KW_TRY);

  scopes_tree_set_contains_try (serializer_get_scope ());

  bool is_raised = jsp_label_raise_nested_jumpable_border ();

  dump_try_for_rewrite ();

  skip_token ();
  current_token_must_be (TOK_OPEN_BRACE);
  skip_token ();

  parse_statement_list ();

  skip_token ();
  current_token_must_be (TOK_CLOSE_BRACE);

  rewrite_try ();

  skip_token ();
  current_token_must_be (TOK_KEYWORD);

  if (is_keyword (KW_CATCH))
  {
    parse_catch_clause ();

    skip_token ();
    if (is_keyword (KW_FINALLY))
    {
      parse_finally_clause ();
    }
    else
    {
      lexer_save_token (tok);
    }
  }
  else if (is_keyword (KW_FINALLY))
  {
    parse_finally_clause ();
  }
  else
  {
    EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Expected either 'catch' or 'finally' token");
  }

  dump_end_try_catch_finally ();

  if (is_raised)
  {
    jsp_label_remove_nested_jumpable_border ();
  }
}

/**
 * iteration_statement
 *  : do_while_statement
 *  | while_statement
 *  | for_statement
 *  | for_in_statement
 *  ;
 */
static void
parse_iterational_statement (jsp_label_t *outermost_named_stmt_label_p) /**< outermost (first) named label,
                                                                         *   corresponding to the statement
                                                                         *   (or NULL, if there are no named
                                                                         *    labels associated with the statement) */
{
  jsp_label_t label;
  jsp_label_push (&label,
                  (jsp_label_type_flag_t) (JSP_LABEL_TYPE_UNNAMED_BREAKS | JSP_LABEL_TYPE_UNNAMED_CONTINUES),
                  TOKEN_EMPTY_INITIALIZER);

  jsp_label_t *outermost_stmt_label_p = (outermost_named_stmt_label_p != NULL ? outermost_named_stmt_label_p : &label);

  if (is_keyword (KW_DO))
  {
    parse_do_while_statement (outermost_stmt_label_p);
  }
  else if (is_keyword (KW_WHILE))
  {
    parse_while_statement (outermost_stmt_label_p);
  }
  else
  {
    JERRY_ASSERT (is_keyword (KW_FOR));
    jsp_parse_for_or_for_in_statement (outermost_stmt_label_p);
  }

  jsp_label_rewrite_jumps_and_pop (&label,
                                   serializer_get_current_instr_counter ());
} /* parse_iterational_statement */

/* statement
  : statement_block
  | variable_statement
  | empty_statement
  | if_statement
  | iteration_statement
  | continue_statement
  | break_statement
  | return_statement
  | with_statement
  | labelled_statement
  | switch_statement
  | throw_statement
  | try_statement
  | expression_statement
  ;

   statement_block
  : '{' LT!* statement_list? LT!* '}'
  ;

   variable_statement
  : 'var' LT!* variable_declaration_list (LT | ';')!
  ;

   empty_statement
  : ';'
  ;

   expression_statement
  : expression (LT | ';')!
  ;

   iteration_statement
  : do_while_statement
  | while_statement
  | for_statement
  | for_in_statement
  ;

   continue_statement
  : 'continue' Identifier? (LT | ';')!
  ;

   break_statement
  : 'break' Identifier? (LT | ';')!
  ;

   return_statement
  : 'return' expression? (LT | ';')!
  ;

   switchStatement
  : 'switch' LT!* '(' LT!* expression LT!* ')' LT!* caseBlock
  ;

   throw_statement
  : 'throw' expression (LT | ';')!
  ;

   try_statement
  : 'try' LT!* '{' LT!* statement_list LT!* '}' LT!* (finally_clause | catch_clause (LT!* finally_clause)?)
  ;*/
static void
parse_statement (jsp_label_t *outermost_stmt_label_p) /**< outermost (first) label, corresponding to the statement
                                                       *   (or NULL, if there are no named labels associated
                                                       *    with the statement) */
{
  dumper_new_statement ();

  if (token_is (TOK_CLOSE_BRACE))
  {
    lexer_save_token (tok);
    return;
  }
  if (token_is (TOK_OPEN_BRACE))
  {
    skip_token ();
    if (!token_is (TOK_CLOSE_BRACE))
    {
      parse_statement_list ();

      skip_token ();
      current_token_must_be (TOK_CLOSE_BRACE);
    }
    return;
  }
  if (is_keyword (KW_VAR))
  {
    parse_variable_declaration_list ();
    if (token_is (TOK_SEMICOLON))
    {
      skip_token ();
    }
    else
    {
      insert_semicolon ();
    }
    return;
  }
  if (is_keyword (KW_FUNCTION))
  {
    parse_function_declaration ();
    return;
  }
  if (token_is (TOK_SEMICOLON))
  {
    return;
  }
  if (is_keyword (KW_CASE) || is_keyword (KW_DEFAULT))
  {
    return;
  }
  if (is_keyword (KW_IF))
  {
    parse_if_statement ();
    return;
  }
  if (is_keyword (KW_DO)
      || is_keyword (KW_WHILE)
      || is_keyword (KW_FOR))
  {
    parse_iterational_statement (outermost_stmt_label_p);
    return;
  }
  if (is_keyword (KW_CONTINUE)
      || is_keyword (KW_BREAK))
  {
    bool is_break = is_keyword (KW_BREAK);

    skip_token ();

    jsp_label_t *label_p;
    bool is_simply_jumpable = true;
    if (!lexer_is_preceded_by_newlines (tok)
        && token_is (TOK_NAME))
    {
      /* break or continue on a label */
      label_p = jsp_label_find (JSP_LABEL_TYPE_NAMED, tok, &is_simply_jumpable);

      if (label_p == NULL)
      {
        EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Label not found");
      }

      skip_token ();
    }
    else if (is_break)
    {
      label_p = jsp_label_find (JSP_LABEL_TYPE_UNNAMED_BREAKS,
                                TOKEN_EMPTY_INITIALIZER,
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
                                TOKEN_EMPTY_INITIALIZER,
                                &is_simply_jumpable);

      if (label_p == NULL)
      {
        EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "No corresponding statement for the continue");
      }
    }

    lexer_save_token (tok);
    insert_semicolon ();

    JERRY_ASSERT (label_p != NULL);

    jsp_label_add_jump (label_p, is_simply_jumpable, is_break);

    return;
  }
  if (is_keyword (KW_RETURN))
  {
    if (serializer_get_scope ()->type != SCOPE_TYPE_FUNCTION)
    {
      EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Return is illegal");
    }

    skip_token ();
    if (!token_is (TOK_SEMICOLON) && !lexer_is_preceded_by_newlines (tok) && !token_is (TOK_CLOSE_BRACE))
    {
      const jsp_operand_t op = parse_expression (true, JSP_EVAL_RET_STORE_NOT_DUMP);
      dump_retval (dump_assignment_of_lhs_if_value_based_reference (op));
      insert_semicolon ();
      return;
    }
    else
    {
      dump_ret ();

      if (token_is (TOK_CLOSE_BRACE))
      {
        lexer_save_token (tok);
      }
      return;
    }
  }
  if (is_keyword (KW_WITH))
  {
    parse_with_statement ();
    return;
  }
  if (is_keyword (KW_SWITCH))
  {
    parse_switch_statement ();
    return;
  }
  if (is_keyword (KW_THROW))
  {
    skip_token ();
    const jsp_operand_t op = parse_expression (true, JSP_EVAL_RET_STORE_NOT_DUMP);
    insert_semicolon ();
    dump_throw (dump_assignment_of_lhs_if_value_based_reference (op));
    return;
  }
  if (is_keyword (KW_TRY))
  {
    parse_try_statement ();
    return;
  }
  if (token_is (TOK_NAME))
  {
    const token temp = tok;
    skip_token ();
    if (token_is (TOK_COLON))
    {
      skip_token ();

      jsp_label_t *label_p = jsp_label_find (JSP_LABEL_TYPE_NAMED, temp, NULL);
      if (label_p != NULL)
      {
        EMIT_ERROR (JSP_EARLY_ERROR_SYNTAX, "Label is duplicated");
      }

      jsp_label_t label;
      jsp_label_push (&label, JSP_LABEL_TYPE_NAMED, temp);

      parse_statement (outermost_stmt_label_p != NULL ? outermost_stmt_label_p : &label);

      jsp_label_rewrite_jumps_and_pop (&label,
                                       serializer_get_current_instr_counter ());
    }
    else
    {
      lexer_save_token (tok);
      tok = temp;
      jsp_operand_t expr = parse_expression (true, JSP_EVAL_RET_STORE_DUMP);
      dump_assignment_of_lhs_if_reference (expr);
      insert_semicolon ();
    }
  }
  else
  {
    parse_expression (true, JSP_EVAL_RET_STORE_DUMP);
    insert_semicolon ();
  }
}

/* source_element
  : function_declaration
  | statement
  ; */
static void
parse_source_element (void)
{
  if (is_keyword (KW_FUNCTION))
  {
    parse_function_declaration ();
  }
  else
  {
    parse_statement_ ();
  }
}

/**
 * Parse source element list
 *
 *  source_element_list
 *   : source_element (LT!* source_element)*
 *   ;
 */
static void
parse_source_element_list (void)
{
  jsp_label_t *prev_label_set_p = jsp_label_new_set ();

  bool is_function = (serializer_get_scope ()->type == SCOPE_TYPE_FUNCTION);


  /*
   * We don't try to perform replacement of local variables with registers for global code, eval code.
   *
   * For global and eval code the replacement can be connected with side effects,
   * that currently can only be figured out in runtime. For example, a variable
   * can be redefined as accessor property of the Global object.
   */
  bool is_try_replace_local_vars_with_regs = is_function;

  const token_type end_tt = is_function? TOK_CLOSE_BRACE : TOK_EOF;

  dumper_new_scope ();

  vm_instr_counter_t scope_code_flags_oc = dump_scope_code_flags_for_rewrite ();

  vm_instr_counter_t reg_var_decl_oc = dump_reg_var_decl_for_rewrite ();

  if (serializer_get_scope ()->type == SCOPE_TYPE_EVAL)
  {
    dump_undefined_assignment (eval_ret_operand ());
  }

  skip_token ();
  while (!token_is (TOK_EOF) && !token_is (TOK_CLOSE_BRACE))
  {
    parse_source_element ();
    skip_token ();
  }

  if (!token_is (end_tt))
  {
    PARSE_ERROR (JSP_EARLY_ERROR_SYNTAX, "Unexpected token", tok.loc);
  }

  lexer_save_token (tok);

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
  if (is_try_replace_local_vars_with_regs
      && fe_scope_tree->type == SCOPE_TYPE_FUNCTION)
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

            reg_var_decl_oc--;
            scope_code_flags_oc--;
            dumper_decrement_function_end_pos ();
          }
        }
      }
    }
  }
#else /* CONFIG_PARSER_ENABLE_PARSE_TIME_BYTE_CODE_OPTIMIZER */
  (void) is_try_replace_local_vars_with_regs;
#endif /* !CONFIG_PARSER_ENABLE_PARSE_TIME_BYTE_CODE_OPTIMIZER */

  rewrite_scope_code_flags (scope_code_flags_oc, scope_flags);
  rewrite_reg_var_decl (reg_var_decl_oc);
  dumper_finish_scope ();

  jsp_label_restore_previous_set (prev_label_set_p);
} /* parse_source_element_list */

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

    parse_source_element_list ();

    skip_token ();
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
