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

#ifndef ECMA_OBJECT_PROTOTYPE_H
#define ECMA_OBJECT_PROTOTYPE_H

#include "ecma-globals.h"

/** \addtogroup ecma ECMA
 * @{
 *
 * \addtogroup ecmabuiltinhelpers ECMA builtin helper operations
 * @{
 */

extern ecma_completion_value_t
ecma_builtin_helper_object_to_string (const ecma_value_t);
extern ecma_completion_value_t
ecma_builtin_helper_get_to_locale_string_at_index (ecma_object_t *, uint32_t);
extern ecma_completion_value_t
ecma_builtin_helper_object_get_properties (ecma_object_t *, bool);
extern ecma_completion_value_t
ecma_builtin_helper_array_concat_value (ecma_object_t *, uint32_t *, ecma_value_t);
extern uint32_t
ecma_builtin_helper_array_index_normalize (ecma_number_t, uint32_t);
extern uint32_t
ecma_builtin_helper_string_index_normalize (ecma_number_t, uint32_t, bool);
extern ecma_completion_value_t
ecma_builtin_helper_string_prototype_object_index_of (ecma_value_t, ecma_value_t,
                                                      ecma_value_t, bool);
extern bool
ecma_builtin_helper_string_find_index (ecma_string_t *, ecma_string_t *, bool, ecma_length_t, ecma_length_t *);
extern ecma_completion_value_t
ecma_builtin_helper_def_prop (ecma_object_t *, ecma_string_t *, ecma_value_t,
                              bool, bool, bool, bool);

#ifndef CONFIG_ECMA_COMPACT_PROFILE_DISABLE_DATE_BUILTIN

/**
 * Time range defines for helper functions.
 *
 * See also:
 *          ECMA-262 v5, 15.9.1.1, 15.9.1.10
 */
/* Hours in a day. */
#define ECMA_DATE_HOURS_PER_DAY         ((ecma_number_t) 24)
/* Minutes in an hour. */
#define ECMA_DATE_MINUTES_PER_HOUR      ((ecma_number_t) 60)
/* Seconds in a minute. */
#define ECMA_DATE_SECONDS_PER_MINUTE    ((ecma_number_t) 60)
/* Milliseconds in a second. */
#define ECMA_DATE_MS_PER_SECOND         ((ecma_number_t) 1000)
/* ECMA_DATE_MS_PER_MINUTE == 60000 */
#define ECMA_DATE_MS_PER_MINUTE         (ECMA_DATE_MS_PER_SECOND * ECMA_DATE_SECONDS_PER_MINUTE)
/* ECMA_DATE_MS_PER_HOUR == 3600000 */
#define ECMA_DATE_MS_PER_HOUR           (ECMA_DATE_MS_PER_MINUTE * ECMA_DATE_MINUTES_PER_HOUR)
/* ECMA_DATE_MS_PER_DAY == 86400000 */
#define ECMA_DATE_MS_PER_DAY            (ECMA_DATE_MS_PER_HOUR * ECMA_DATE_HOURS_PER_DAY)
/* This gives a range of 8,640,000,000,000,000 milliseconds
 * to either side of 01 January, 1970 UTC.
 */
#define ECMA_DATE_MAX_VALUE             8.64e15

/**
 * Timezone type.
 */
typedef enum
{
  ECMA_DATE_UTC, /**< date vaule is in UTC */
  ECMA_DATE_LOCAL /**< date vaule is in local time */
} ecma_date_timezone_t;

/* ecma-builtin-helpers-date.cpp */
extern ecma_number_t ecma_date_day (ecma_number_t);
extern ecma_number_t ecma_date_time_within_day (ecma_number_t);
extern ecma_number_t ecma_date_days_in_year (ecma_number_t);
extern ecma_number_t ecma_date_day_from_year (ecma_number_t);
extern ecma_number_t ecma_date_time_from_year (ecma_number_t);
extern ecma_number_t ecma_date_year_from_time (ecma_number_t);
extern ecma_number_t ecma_date_in_leap_year (ecma_number_t);
extern ecma_number_t ecma_date_day_within_year (ecma_number_t);
extern ecma_number_t ecma_date_month_from_time (ecma_number_t);
extern ecma_number_t ecma_date_date_from_time (ecma_number_t);
extern ecma_number_t ecma_date_week_day (ecma_number_t);
extern ecma_number_t ecma_date_local_tza ();
extern ecma_number_t ecma_date_daylight_saving_ta (ecma_number_t);
extern ecma_number_t ecma_date_local_time (ecma_number_t);
extern ecma_number_t ecma_date_utc (ecma_number_t);
extern ecma_number_t ecma_date_hour_from_time (ecma_number_t);
extern ecma_number_t ecma_date_min_from_time (ecma_number_t);
extern ecma_number_t ecma_date_sec_from_time (ecma_number_t);
extern ecma_number_t ecma_date_ms_from_time (ecma_number_t);
extern ecma_number_t ecma_date_make_time (ecma_number_t, ecma_number_t, ecma_number_t, ecma_number_t);
extern ecma_number_t ecma_date_make_day (ecma_number_t, ecma_number_t, ecma_number_t);
extern ecma_number_t ecma_date_make_date (ecma_number_t, ecma_number_t);
extern ecma_number_t ecma_date_time_clip (ecma_number_t);
extern ecma_number_t ecma_date_timezone_offset (ecma_number_t);
extern ecma_completion_value_t ecma_date_set_internal_property (ecma_value_t, ecma_number_t,
                                                                ecma_number_t, ecma_date_timezone_t);
extern void ecma_date_insert_leading_zeros (ecma_string_t **, ecma_number_t, uint32_t);

extern ecma_completion_value_t ecma_date_value_to_string (ecma_number_t);
extern ecma_completion_value_t ecma_date_value_to_utc_string (ecma_number_t);
extern ecma_completion_value_t ecma_date_value_to_iso_string (ecma_number_t);
extern ecma_completion_value_t ecma_date_value_to_date_string (ecma_number_t);
extern ecma_completion_value_t ecma_date_value_to_time_string (ecma_number_t);
extern ecma_completion_value_t ecma_date_get_primitive_value (ecma_value_t);

#endif /* !CONFIG_ECMA_COMPACT_PROFILE_DISABLE_DATE_BUILTIN */

/* ecma-builtin-helper-json.cpp */

/**
 * Context for JSON.stringify()
 */
typedef struct
{
  /** Collection for property keys. */
  ecma_collection_header_t *property_list_p;

  /** Collection for traversing objects. */
  ecma_collection_header_t *occurence_stack_p;

  /** The actual indentation text. */
  ecma_string_t *indent_str_p;

  /** The indentation text. */
  ecma_string_t *gap_str_p;

  /** The replacer function. */
  ecma_object_t *replacer_function_p;
} ecma_json_stringify_context_t;

extern bool ecma_has_object_value_in_collection (ecma_collection_header_t *, ecma_value_t);
extern bool ecma_has_string_value_in_collection (ecma_collection_header_t *, ecma_value_t);

extern ecma_string_t *ecma_builtin_helper_json_create_hex_digit_ecma_string (uint8_t);

extern ecma_string_t *
ecma_builtin_helper_json_create_separated_properties (ecma_collection_header_t *, ecma_string_t *);
extern ecma_completion_value_t
ecma_builtin_helper_json_create_formatted_json (ecma_string_t *, ecma_string_t *, ecma_string_t *,
                                                ecma_collection_header_t *, ecma_json_stringify_context_t *);
extern ecma_completion_value_t
ecma_builtin_helper_json_create_non_formatted_json (ecma_string_t *, ecma_string_t *, ecma_collection_header_t *);

/**
 * @}
 * @}
 */

#endif /* !ECMA_OBJECT_PROPERTY_H */
