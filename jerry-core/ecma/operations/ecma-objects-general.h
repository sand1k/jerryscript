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

#ifndef ECMA_OBJECTS_GENERAL_H
#define ECMA_OBJECTS_GENERAL_H

#include "ecma-conversion.h"
#include "ecma-globals.h"

/** \addtogroup ecma ECMA
 * @{
 *
 * \addtogroup ecmaobjectsinternalops ECMA objects' operations
 * @{
 */

extern ecma_completion_value_t ecma_reject (bool);
extern ecma_object_t *ecma_op_create_object_object_noarg (void);
extern ecma_completion_value_t ecma_op_create_object_object_arg (ecma_value_t);
extern ecma_object_t *ecma_op_create_object_object_noarg_and_set_prototype (ecma_object_t *);

extern ecma_completion_value_t ecma_op_general_object_get (ecma_object_t *, ecma_string_t *);
extern ecma_property_t *ecma_op_general_object_get_own_property (ecma_object_t *, ecma_string_t *);
extern ecma_property_t *ecma_op_general_object_get_property (ecma_object_t *, ecma_string_t *);
extern ecma_completion_value_t ecma_op_general_object_put (ecma_object_t *, ecma_string_t *, ecma_value_t, bool);
extern bool ecma_op_general_object_can_put (ecma_object_t *, ecma_string_t *);
extern ecma_completion_value_t ecma_op_general_object_delete (ecma_object_t *, ecma_string_t *, bool);
extern ecma_completion_value_t ecma_op_general_object_default_value (ecma_object_t *, ecma_preferred_type_hint_t);
extern ecma_completion_value_t
ecma_op_general_object_define_own_property (ecma_object_t *, ecma_string_t *, const ecma_property_descriptor_t *, bool);

/**
 * @}
 * @}
 */

#endif /* !ECMA_OBJECTS_GENERAL_H */
