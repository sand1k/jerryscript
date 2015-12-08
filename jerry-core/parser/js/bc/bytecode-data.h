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

#ifndef BYTECODE_DATA_H
#define BYTECODE_DATA_H

#include "opcodes.h"
#include "mem-allocator.h"
#include "lit-id-hash-table.h"
#include "scopes-tree.h"

/*
 * All literals are kept in the 'literals' array.
 * Literal structure doesn't hold real string. All program-specific strings
 * are kept in the 'strings_buffer' and literal has pointer to this buffer.
 *
 * Literal id is its index in 'literals' array of bytecode_data_t structure.
 *
 * Bytecode, which is kept in the 'instrs' field, is divided into blocks
 * of 'BLOCK_SIZE' operands. Every block has its own numbering of literals.
 * Literal uid could be in range [0, 127] in every block.
 *
 * To map uid to literal id 'lit_id_hash' table is used.
 */
#define BLOCK_SIZE 64u

/**
 * Header of byte-code memory region, containing byte-code array and literal identifiers hash table
 */
typedef struct __attribute__ ((aligned (MEM_ALIGNMENT))) bytecode_data_header_t
{
  vm_instr_t *instrs_p; /**< pointer to the bytecode */
  vm_instr_counter_t instrs_count; /**< number of instructions in the byte-code array */
  mem_cpointer_t lit_id_hash_cp; /**< pointer to literal identifiers hash table
                                  *   See also: lit_id_hash_table_init */

  mem_cpointer_t func_decls_cp; /**< declrations inside current scope */
  uint16_t func_decls_count; /**< cound of function declarations inside current scope */
  // mem_cpointer_t scope_func_exprs_cp; /**< function expressions inside current scope */
  // uint16_t func_exprs_count;

  mem_cpointer_t next_header_cp; /**< pointer to next instructions data header */
} bytecode_data_header_t;


bytecode_data_header_t * bc_get_first_bytecode_data_header ();

void
bc_add_bytecode_data (bytecode_data_header_t *bc_header_p,
                      lit_id_hash_table *lit_id_hash_table_p,
                      vm_instr_t *bytecode_p,
                      vm_instr_counter_t instrs_count,
                      lit_cpointer_t *func_decls_p,
                      uint16_t func_decls_count);

void bc_remove_bytecode_data (const bytecode_data_header_t *);

vm_instr_t bc_get_instr (const bytecode_data_header_t *,
                         vm_instr_counter_t);

void bc_print_instrs (const bytecode_data_header_t *bytecode_data_p);

const bytecode_data_header_t *bc_merge_scopes_into_bytecode (scopes_tree, bool);
bytecode_data_header_t *bc_dump_scopes (scopes_tree, bool);

void bc_finalize ();

lit_cpointer_t
bc_get_literal_cp_by_uid (uint8_t,
                          const bytecode_data_header_t *,
                          vm_instr_counter_t);


#ifdef JERRY_ENABLE_SNAPSHOT
/*
 * Snapshot-related
 */
bool bc_save_bytecode_with_idx_map (uint8_t *, size_t, size_t *, const bytecode_data_header_t *,
                                    const lit_mem_to_snapshot_id_map_entry_t *, uint32_t,
                                    uint32_t *, uint32_t *);

const bytecode_data_header_t *
bc_load_bytecode_with_idx_map (const uint8_t *, uint32_t, uint32_t,
                               const lit_mem_to_snapshot_id_map_entry_t *, uint32_t, bool);
#endif /* JERRY_ENABLE_SNAPSHOT */

#endif /* BYTECODE_DATA_H */
