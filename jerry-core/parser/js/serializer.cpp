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

#include "lit-id-hash-table.h"
#include "serializer.h"
#include "bytecode-data.h"
#include "pretty-printer.h"
#include "array-list.h"
#include "scopes-tree.h"

static scopes_tree current_scope = NULL;

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
serializer_get_literal_cp_by_uid (uint8_t id, /**< literal idx */
                                  const bytecode_data_header_t *bytecode_data_p, /**< pointer to bytecode */
                                  vm_instr_counter_t oc) /**< position in the bytecode */
{
  JERRY_ASSERT (bytecode_data_p);

  lit_id_hash_table *lit_id_hash = null_hash;
  lit_id_hash = MEM_CP_GET_POINTER (lit_id_hash_table, bytecode_data_p->lit_id_hash_cp);

  if (lit_id_hash == null_hash)
  {
    return INVALID_LITERAL;
  }

  return lit_id_hash_table_lookup (lit_id_hash, id, oc);
} /* serializer_get_literal_cp_by_uid */

void
serializer_set_scope (scopes_tree new_scope)
{
  current_scope = new_scope;
}



vm_instr_counter_t
serializer_get_current_instr_counter (void)
{
  return scopes_tree_instrs_num (current_scope);
}

vm_instr_counter_t
serializer_count_instrs_in_subscopes (void)
{
  return (vm_instr_counter_t) (scopes_tree_count_instructions (current_scope) - scopes_tree_instrs_num (current_scope));
}

void
serializer_free (void)
{
  lit_finalize ();
  jsp_bc_finalize ();
}

#ifdef JERRY_ENABLE_SNAPSHOT
/**
 * Dump byte-code and idx-to-literal map to snapshot
 *
 * @return true, upon success (i.e. buffer size is enough),
 *         false - otherwise.
 */
bool
serializer_dump_bytecode_with_idx_map (uint8_t *buffer_p, /**< buffer to dump to */
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
serializer_load_bytecode_with_idx_map (const uint8_t *bytecode_and_idx_map_p, /**< buffer with instructions array
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
    jsp_bc_add_bytecode_data (header_p,
                              (lit_id_hash_table *) lit_id_hash_table_buffer_p,
                              instrs_p,
                              (vm_instr_counter_t) instructions_number);

    return header_p;
  }
  else
  {
    mem_heap_free_block (buffer_p);
    return NULL;
  }
} /* serializer_load_bytecode_with_idx_map */

#endif /* JERRY_ENABLE_SNAPSHOT */
