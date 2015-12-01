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

static bytecode_data_header_t *first_bytecode_header_p = NULL;

bytecode_data_header_t *
jsp_bc_get_first_bytecode_data_header ()
{
  return first_bytecode_header_p;
} /* jsp_bc_get_first_bytecode_header */

void
jsp_bc_add_bytecode_data (bytecode_data_header_t *bc_header_p,
                          lit_id_hash_table *lit_id_hash_table_p,
                          vm_instr_t *bytecode_p,
                          vm_instr_counter_t instrs_count)
{
  MEM_CP_SET_POINTER (bc_header_p->lit_id_hash_cp, lit_id_hash_table_p);
  bc_header_p->instrs_p = bytecode_p;
  bc_header_p->instrs_count = instrs_count;
  MEM_CP_SET_POINTER (bc_header_p->next_header_cp, first_bytecode_header_p);

  first_bytecode_header_p = bc_header_p;
} /* jsp_bc_add_bytecode */

/**
 * Deletes bytecode and associated hash table
 */
void
jsp_bc_remove_bytecode_data (const bytecode_data_header_t *bytecode_data_p)
{
  bytecode_data_header_t *prev_header = NULL;
  bytecode_data_header_t *cur_header_p = first_bytecode_header_p;

  while (cur_header_p != NULL)
  {
    if (cur_header_p == bytecode_data_p)
    {
      if (prev_header)
      {
        prev_header->next_header_cp = cur_header_p->next_header_cp;
      }
      else
      {
        first_bytecode_header_p = MEM_CP_GET_POINTER (bytecode_data_header_t, cur_header_p->next_header_cp);
      }
      mem_heap_free_block (cur_header_p);
      break;
    }

    prev_header = cur_header_p;
    cur_header_p = MEM_CP_GET_POINTER (bytecode_data_header_t, cur_header_p->next_header_cp);
  }
} /* jsp_bc_remove_bytecode_data */

void
jsp_bc_finalize ()
{
  while (first_bytecode_header_p != NULL)
  {
    bytecode_data_header_t *header_p = first_bytecode_header_p;
    first_bytecode_header_p = MEM_CP_GET_POINTER (bytecode_data_header_t, header_p->next_header_cp);

    mem_heap_free_block (header_p);
  }
} /* jsp_bc_finalize */

