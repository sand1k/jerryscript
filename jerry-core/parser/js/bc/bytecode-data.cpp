/* Copyright 2015 Samsung Electronics Co., Ltd.
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
#include "pretty-printer.h"
#include "opcodes-dumper.h"

static bytecode_data_header_t *first_bytecode_header_p = NULL;

static void
bc_add_bytecode_data (bytecode_data_header_t *bc_header_p, /**< byte-code scope data header */
                      lit_id_hash_table *lit_id_hash_table_p, /**< (idx, block id) -> literal hash table */
                      vm_instr_t *bytecode_p, /**< byte-code instructions array */
                      mem_cpointer_t *declarations_p, /**< array of function / variable declarations */
                      uint16_t func_scopes_count, /**< number of function declarations / expressions
                                                   *   located immediately in the corresponding scope */
                      uint16_t var_decls_count, /**< number of variable declarations immediately in the scope */
                      bool is_strict, /**< is the scope's code strict mode code? */
                      bool is_ref_arguments_identifier, /**< does the scope's code
                                                        *    reference 'arguments' identifier? */
                      bool is_ref_eval_identifier, /**< does the scope's code
                                                    *   reference 'eval' identifier? */
                      bool is_arguments_moved_to_regs, /**< is it function scope, for which arguments
                                                        *   are located on registers, not in variables? */
                      bool is_no_lex_env) /**< is lexical environment unused in the scope? */
{
  MEM_CP_SET_POINTER (bc_header_p->lit_id_hash_cp, lit_id_hash_table_p);
  bc_header_p->instrs_p = bytecode_p;
  bc_header_p->instrs_count = 0;
  MEM_CP_SET_POINTER (bc_header_p->declarations_cp, declarations_p);
  bc_header_p->func_scopes_count = func_scopes_count;
  bc_header_p->var_decls_count = var_decls_count;
  bc_header_p->next_header_cp = MEM_CP_NULL;

  bc_header_p->is_strict = is_strict;
  bc_header_p->is_ref_arguments_identifier = is_ref_arguments_identifier;
  bc_header_p->is_ref_eval_identifier = is_ref_eval_identifier;
  bc_header_p->is_args_moved_to_regs = is_arguments_moved_to_regs;
  bc_header_p->is_no_lex_env = is_no_lex_env;
} /* bc_add_bytecode_data */

static void
bc_free_bytecode_data (bytecode_data_header_t *bytecode_data_p) /**< byte-code scope data header */
{
  bytecode_data_header_t *next_to_handle_list_p = bytecode_data_p;

  while (next_to_handle_list_p != NULL)
  {
    bytecode_data_header_t *bc_header_list_iter_p = next_to_handle_list_p;
    next_to_handle_list_p = NULL;

    while (bc_header_list_iter_p != NULL)
    {
      bytecode_data_header_t *header_p = bc_header_list_iter_p;

      bc_header_list_iter_p = MEM_CP_GET_POINTER (bytecode_data_header_t, header_p->next_header_cp);

      mem_cpointer_t *declarations_p = MEM_CP_GET_POINTER (mem_cpointer_t, header_p->declarations_cp);

      for (uint32_t index = 0; index < header_p->func_scopes_count; index++)
      {
        bytecode_data_header_t *child_scope_header_p = MEM_CP_GET_NON_NULL_POINTER (bytecode_data_header_t,
                                                                                    declarations_p[index]);
        JERRY_ASSERT (child_scope_header_p->next_header_cp == MEM_CP_NULL);

        MEM_CP_SET_POINTER (child_scope_header_p->next_header_cp, next_to_handle_list_p);

        next_to_handle_list_p = child_scope_header_p;
      }

      mem_heap_free_block (header_p);
    }

    JERRY_ASSERT (bc_header_list_iter_p == NULL);
  }
} /* bc_free_bytecode_data */

/**
 * Deletes bytecode and associated hash table
 */
void
bc_remove_bytecode_data (const bytecode_data_header_t *bytecode_data_p) /**< byte-code scope data header */
{
  bytecode_data_header_t *prev_header_p = NULL;
  bytecode_data_header_t *cur_header_p = first_bytecode_header_p;

  while (cur_header_p != NULL)
  {
    if (cur_header_p == bytecode_data_p)
    {
      if (prev_header_p)
      {
        prev_header_p->next_header_cp = cur_header_p->next_header_cp;
      }
      else
      {
        first_bytecode_header_p = MEM_CP_GET_POINTER (bytecode_data_header_t, cur_header_p->next_header_cp);
      }

      cur_header_p->next_header_cp = MEM_CP_NULL;

      bc_free_bytecode_data (cur_header_p);

      break;
    }

    prev_header_p = cur_header_p;
    cur_header_p = MEM_CP_GET_POINTER (bytecode_data_header_t, cur_header_p->next_header_cp);
  }
} /* bc_remove_bytecode_data */

vm_instr_t bc_get_instr (const bytecode_data_header_t *bytecode_data_p, /**< byte-code scope data header */
                         vm_instr_counter_t oc) /**< instruction position */
{
  JERRY_ASSERT (oc < bytecode_data_p->instrs_count);
  return bytecode_data_p->instrs_p[oc];
}

void
bc_print_instrs (const bytecode_data_header_t *bytecode_data_p) /**< byte-code scope data header */
{
#ifdef JERRY_ENABLE_PRETTY_PRINTER
  for (vm_instr_counter_t loc = 0; loc < bytecode_data_p->instrs_count; loc++)
  {
    op_meta opm;

    opm.op = bytecode_data_p->instrs_p[loc];
    for (int i = 0; i < 3; i++)
    {
      opm.lit_id[i] = NOT_A_LITERAL;
    }

    pp_op_meta (bytecode_data_p, loc, opm, false);
  }
#else
  (void) bytecode_data_p;
#endif
}

/**
 * Dump single scopes tree into bytecode
 *
 * @return pointer to bytecode header of the outer most scope
 */
static bytecode_data_header_t *
bc_dump_single_scope (scopes_tree scope_p) /**< a node of scopes tree */
{
  const size_t entries_count = scope_p->max_uniq_literals_num;
  const vm_instr_counter_t instrs_count = scopes_tree_instrs_num (scope_p);
  const size_t blocks_count = JERRY_ALIGNUP (instrs_count, BLOCK_SIZE) / BLOCK_SIZE;
  const size_t func_scopes_count = scopes_tree_child_scopes_num (scope_p);
  const uint16_t var_decls_count = linked_list_get_length (scope_p->var_decls);
  const size_t bytecode_size = JERRY_ALIGNUP (instrs_count * sizeof (vm_instr_t), MEM_ALIGNMENT);
  const size_t hash_table_size = lit_id_hash_table_get_size_for_table (entries_count, blocks_count);
  const size_t declarations_area_size = JERRY_ALIGNUP (func_scopes_count * sizeof (mem_cpointer_t)
                                                       + var_decls_count * sizeof (lit_cpointer_t),
                                                       MEM_ALIGNMENT);
  const size_t header_and_tables_size = JERRY_ALIGNUP ((sizeof (bytecode_data_header_t)
                                                        + hash_table_size
                                                        + declarations_area_size),
                                                       MEM_ALIGNMENT);

  uint8_t *buffer_p = (uint8_t *) mem_heap_alloc_block (bytecode_size + header_and_tables_size,
                                                        MEM_HEAP_ALLOC_LONG_TERM);

  lit_id_hash_table *lit_id_hash_p = lit_id_hash_table_init (buffer_p + sizeof (bytecode_data_header_t),
                                                             hash_table_size,
                                                             entries_count, blocks_count);

  mem_cpointer_t *declarations_p = (mem_cpointer_t *) (buffer_p + sizeof (bytecode_data_header_t) + hash_table_size);

  scopes_tree_dump_var_decls (scope_p, (lit_cpointer_t *) (declarations_p + func_scopes_count));

  vm_instr_t *bytecode_p = (vm_instr_t *) (buffer_p + header_and_tables_size);

  JERRY_ASSERT (scope_p->max_uniq_literals_num >= lit_id_hash_p->current_bucket_pos);

  bytecode_data_header_t *header_p = (bytecode_data_header_t *) buffer_p;

  if ((uint16_t) func_scopes_count != func_scopes_count)
  {
    jerry_fatal (ERR_OUT_OF_MEMORY);
  }

  bc_add_bytecode_data (header_p,
                        lit_id_hash_p, bytecode_p,
                        declarations_p,
                        (uint16_t) func_scopes_count,
                        var_decls_count,
                        scope_p->strict_mode,
                        scope_p->ref_arguments,
                        scope_p->ref_eval,
                        scope_p->is_args_moved_to_regs,
                        scope_p->is_no_lex_env);

  JERRY_ASSERT (scope_p->bc_header_cp == MEM_CP_NULL);
  MEM_CP_SET_NON_NULL_POINTER (scope_p->bc_header_cp, header_p);

  return header_p;
} /* bc_dump_single_scope */

static bytecode_data_header_t *
bc_dump_scope_and_prepare_header (scopes_tree scope_p) /**< a node of scopes tree */
{
  bytecode_data_header_t *header_p = bc_dump_single_scope (scope_p);
  JERRY_ASSERT (header_p->next_header_cp == MEM_CP_NULL);

  mem_cpointer_t *declarations_p = MEM_CP_GET_POINTER (mem_cpointer_t, header_p->declarations_cp);

  uint32_t index = 0;
  scopes_tree child_scopes_iter_p = MEM_CP_GET_POINTER (scopes_tree_int, scope_p->children_list_cp);

  while (child_scopes_iter_p != NULL)
  {
    JERRY_ASSERT (index < header_p->func_scopes_count);

    MEM_CP_SET_POINTER (declarations_p[index], child_scopes_iter_p);

    index++;

    scopes_tree next_child_scope_p = MEM_CP_GET_POINTER (scopes_tree_int, child_scopes_iter_p->next_scope_cp);

    child_scopes_iter_p = next_child_scope_p;
  }

  JERRY_ASSERT (index == header_p->func_scopes_count);

  return header_p;
} /* bc_dump_scope_and_prepare_header */

/**
 * Dump scopes tree into bytecode
 *
 * See also:
 *          Note to declarations_cp field of bytecode_data_header_t
 *
 * @return pointer to bytecode header of the outer most scope
 */
bytecode_data_header_t *
bc_alloc_headers_from_scopes_tree (scopes_tree scope_p) /**< a node of scopes tree */
{
  bytecode_data_header_t *bc_header_p = bc_dump_scope_and_prepare_header (scope_p);

  bytecode_data_header_t *next_to_handle_list_p = bc_header_p;

  while (next_to_handle_list_p != NULL)
  {
    bytecode_data_header_t *bc_header_list_iter_p = next_to_handle_list_p;

    next_to_handle_list_p = NULL;

    while (bc_header_list_iter_p != NULL)
    {
      mem_cpointer_t *declarations_p = MEM_CP_GET_POINTER (mem_cpointer_t, bc_header_list_iter_p->declarations_cp);

      for (uint32_t index = 0; index < bc_header_list_iter_p->func_scopes_count; index++)
      {
        scopes_tree next_tree_p = MEM_CP_GET_NON_NULL_POINTER (scopes_tree_int, declarations_p[index]);

        bytecode_data_header_t *next_header_p = bc_dump_scope_and_prepare_header (next_tree_p);

        MEM_CP_SET_NON_NULL_POINTER (declarations_p[index], next_header_p);

        JERRY_ASSERT (next_header_p->next_header_cp == MEM_CP_NULL);

        MEM_CP_SET_POINTER (next_header_p->next_header_cp, next_to_handle_list_p);
        next_to_handle_list_p = next_header_p;
      }

      bytecode_data_header_t *next_bc_header_list_iter_p = MEM_CP_GET_POINTER (bytecode_data_header_t,
                                                                               bc_header_list_iter_p->next_header_cp);
      bc_header_list_iter_p->next_header_cp = MEM_CP_NULL;

      bc_header_list_iter_p = next_bc_header_list_iter_p;
    }

    JERRY_ASSERT (bc_header_list_iter_p == NULL);
    bc_header_list_iter_p = next_to_handle_list_p;
  }

  MEM_CP_SET_POINTER (bc_header_p->next_header_cp, first_bytecode_header_p);
  first_bytecode_header_p = bc_header_p;

  return bc_header_p;
} /* bc_alloc_headers_from_scopes_tree */

void
bc_finalize (void)
{
  while (first_bytecode_header_p != NULL)
  {
    bytecode_data_header_t *header_p = first_bytecode_header_p;
    first_bytecode_header_p = MEM_CP_GET_POINTER (bytecode_data_header_t, header_p->next_header_cp);

    header_p->next_header_cp = MEM_CP_NULL;

    bc_free_bytecode_data (header_p);
  }
} /* bc_finalize */

/**
 * Convert literal id (operand value of instruction) to compressed pointer to literal
 *
 * Bytecode is divided into blocks of fixed size and each block has independent encoding of variable names,
 * which are represented by 8 bit numbers - ids.
 * This function performs conversion from id to literal.
 *
 * @return compressed pointer to literal
 */
lit_cpointer_t
bc_get_literal_cp_by_uid (uint8_t id, /**< literal idx */
                          const bytecode_data_header_t *bytecode_data_p, /**< pointer to bytecode */
                          vm_instr_counter_t oc) /**< position in the bytecode */
{
  JERRY_ASSERT (bytecode_data_p);

  lit_id_hash_table *lit_id_hash = MEM_CP_GET_POINTER (lit_id_hash_table, bytecode_data_p->lit_id_hash_cp);

  if (lit_id_hash == NULL)
  {
    return INVALID_LITERAL;
  }

  return lit_id_hash_table_lookup (lit_id_hash, id, oc);
} /* serializer_get_literal_cp_by_uid */

#ifdef JERRY_ENABLE_SNAPSHOT
/**
 * Dump byte-code and idx-to-literal map to snapshot
 *
 * @return true, upon success (i.e. buffer size is enough),
 *         false - otherwise.
 */
bool
bc_save_bytecode_with_idx_map (uint8_t *buffer_p, /**< buffer to dump to */
                               size_t buffer_size, /**< buffer size */
                               size_t *in_out_buffer_offset_p, /**< in-out: buffer write offset */
                               const bytecode_data_header_t *bytecode_data_p, /**< byte-code data */
                               const lit_mem_to_snapshot_id_map_entry_t *lit_map_p, /**< map from literal
                                                                                     *   identifiers in
                                                                                     *   literal storage
                                                                                     *   to literal offsets
                                                                                     *   in snapshot */
                               uint32_t literals_num, /**< literals number */
                               uint32_t *out_bytecode_size_p, /**< out: size of dumped instructions array */
                               uint32_t *out_idx_to_lit_map_size_p) /**< out: side of dumped
                                                                     *        idx to literals map */
{
  JERRY_ASSERT (bytecode_data_p->next_header_cp == MEM_CP_NULL);

  vm_instr_counter_t instrs_num = bytecode_data_p->instrs_count;

  const size_t instrs_array_size = sizeof (vm_instr_t) * instrs_num;
  if (*in_out_buffer_offset_p + instrs_array_size > buffer_size)
  {
    return false;
  }
  memcpy (buffer_p + *in_out_buffer_offset_p, bytecode_data_p->instrs_p, instrs_array_size);
  *in_out_buffer_offset_p += instrs_array_size;

  *out_bytecode_size_p = (uint32_t) (sizeof (vm_instr_t) * instrs_num);

  lit_id_hash_table *lit_id_hash_p = MEM_CP_GET_POINTER (lit_id_hash_table, bytecode_data_p->lit_id_hash_cp);
  uint32_t idx_to_lit_map_size = lit_id_hash_table_dump_for_snapshot (buffer_p,
                                                                      buffer_size,
                                                                      in_out_buffer_offset_p,
                                                                      lit_id_hash_p,
                                                                      lit_map_p,
                                                                      literals_num,
                                                                      instrs_num);

  if (idx_to_lit_map_size == 0)
  {
    return false;
  }
  else
  {
    *out_idx_to_lit_map_size_p = idx_to_lit_map_size;

    return true;
  }
} /* serializer_dump_bytecode_with_idx_map */

/**
 * Register bytecode and idx map from snapshot
 *
 * NOTE:
 *      If is_copy flag is set, bytecode is copied from snapshot, else bytecode is referenced directly
 *      from snapshot
 *
 * @return pointer to byte-code header, upon success,
 *         NULL - upon failure (i.e., in case snapshot format is not valid)
 */
const bytecode_data_header_t *
bc_load_bytecode_with_idx_map (const uint8_t *bytecode_and_idx_map_p, /**< buffer with instructions array
                                                                       *   and idx to literals map from
                                                                       *   snapshot */
                               uint32_t bytecode_size, /**< size of instructions array */
                               uint32_t idx_to_lit_map_size, /**< size of the idx to literals map */
                               const lit_mem_to_snapshot_id_map_entry_t *lit_map_p, /**< map of in-snapshot
                                                                                     *   literal offsets
                                                                                     *   to literal identifiers,
                                                                                     *   created in literal
                                                                                     *   storage */
                               uint32_t literals_num, /**< number of literals */
                               bool is_copy) /** flag, indicating whether the passed in-snapshot data
                                              *  should be copied to engine's memory (true),
                                              *  or it can be referenced until engine is stopped
                                              *  (i.e. until call to jerry_cleanup) */
{
  const uint8_t *idx_to_lit_map_p = bytecode_and_idx_map_p + bytecode_size;

  size_t instructions_number = bytecode_size / sizeof (vm_instr_t);
  size_t blocks_count = JERRY_ALIGNUP (instructions_number, BLOCK_SIZE) / BLOCK_SIZE;

  uint32_t idx_num_total;
  size_t idx_to_lit_map_offset = 0;
  if (!jrt_read_from_buffer_by_offset (idx_to_lit_map_p,
                                       idx_to_lit_map_size,
                                       &idx_to_lit_map_offset,
                                       &idx_num_total))
  {
    return NULL;
  }

  const size_t bytecode_alloc_size = JERRY_ALIGNUP (bytecode_size, MEM_ALIGNMENT);
  const size_t hash_table_size = lit_id_hash_table_get_size_for_table (idx_num_total, blocks_count);
  const size_t header_and_hash_table_size = JERRY_ALIGNUP (sizeof (bytecode_data_header_t) + hash_table_size,
                                                           MEM_ALIGNMENT);
  const size_t alloc_size = header_and_hash_table_size + (is_copy ? bytecode_alloc_size : 0);

  uint8_t *buffer_p = (uint8_t*) mem_heap_alloc_block (alloc_size, MEM_HEAP_ALLOC_LONG_TERM);
  bytecode_data_header_t *header_p = (bytecode_data_header_t *) buffer_p;

  vm_instr_t *instrs_p;
  vm_instr_t *snapshot_instrs_p = (vm_instr_t *) bytecode_and_idx_map_p;
  if (is_copy)
  {
    instrs_p = (vm_instr_t *) (buffer_p + header_and_hash_table_size);
    memcpy (instrs_p, snapshot_instrs_p, bytecode_size);
  }
  else
  {
    instrs_p = snapshot_instrs_p;
  }

  uint8_t *lit_id_hash_table_buffer_p = buffer_p + sizeof (bytecode_data_header_t);
  if (lit_id_hash_table_load_from_snapshot (blocks_count,
                                            idx_num_total,
                                            idx_to_lit_map_p + idx_to_lit_map_offset,
                                            idx_to_lit_map_size - idx_to_lit_map_offset,
                                            lit_map_p,
                                            literals_num,
                                            lit_id_hash_table_buffer_p,
                                            hash_table_size)
      && (vm_instr_counter_t) instructions_number == instructions_number)
  {
    bc_add_bytecode_data (header_p,
                          (lit_id_hash_table *) lit_id_hash_table_buffer_p,
                          instrs_p,
                          NULL, /* FIXME: declarations */
                          0, /* FIXME: func scopes count*/
                          0, /* FIXME: var declarations count */
                          /* FIXME: scope_p->strict_mode */ false,
                          /* FIXME: scope_p->ref_arguments */ false,
                          /* FIXME: scope_p->ref_eval */ false,
                          /* FIXME: scope_p->is_args_moved_to_regs */ false,
                          /* FIXME: scope_p->is_no_lex_env */ false);

    return header_p;
  }
  else
  {
    mem_heap_free_block (buffer_p);
    return NULL;
  }
} /* serializer_load_bytecode_with_idx_map */

#endif /* JERRY_ENABLE_SNAPSHOT */
