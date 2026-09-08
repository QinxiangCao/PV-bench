#ifndef PVBENCH_ENGINEERING_STRING_H
#define PVBENCH_ENGINEERING_STRING_H

#include "char_array_def.h"

/*@ Import Coq Require Import SimpleC.StdLib.string_lib */

/*@ Extern Coq (store_string : Z -> list Z -> Assertion)
               (all_ascii : list Z -> Prop)
               (no_inner_nul : list Z -> Prop)
               (valid_string : list Z -> Prop)
               (c_string : list Z -> list Z)
               (string_length : list Z -> Z)
               (memchr_result : list Z -> Z -> Z -> Z -> Z -> Prop)
               (strchr_result : list Z -> Z -> Z -> Z -> Prop)
               (strcmp_result : list Z -> list Z -> Z -> Prop)
               (strncmp_result : list Z -> list Z -> Z -> Z -> Prop)
               (strncpy_content : list Z -> Z -> list Z -> Prop)
               (strncat_result : list Z -> list Z -> Z -> list Z -> Prop)
 */

/*@ include strategies "string.strategies" */

#endif
