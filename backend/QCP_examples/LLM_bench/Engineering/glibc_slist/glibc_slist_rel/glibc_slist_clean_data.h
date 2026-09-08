struct list {
    int data;
    struct list *next;
};

#include "safeexecE_def.h"

/*@ Extern Coq (listrep : Z -> Assertion)
               (lseg : Z -> Z -> Assertion)
               (sll : Z -> list Z -> Assertion)
               (sllseg : Z -> Z -> list Z -> Assertion)
               (sllbseg : Z -> Z -> list Z -> Assertion)
               (sll_tag : Z -> Prop)
 */

/*@ Import Coq From SimpleC.EE.QCP_demos_LLM Require Import sll_lib */
/*@ Import Coq Require Import glibc_slist_lib */
/*@ include strategies "sll.strategies" */

/*@ Extern Coq (maketuple: {A} {B} -> A -> B -> (A * B))
               (list_tail_M: list Z -> program unit (list Z * Z))
               (list_append_raw_M : list Z -> list Z -> program unit (list Z))
               (glibc_slist_clean_merge_M : list Z -> list Z -> program unit (list Z))
               (glibc_slist_clean_free_M : list Z -> program unit unit)
 */

struct list *malloc_list_node(int data)
/*@ With data0
    Require data == data0 && emp 
    Ensure __return != 0 && __return -> data == data0 && __return -> next == 0
*/;
void free_list_node(struct list *x)
/*@ With d n
    Require x -> data == d && x -> next == n
    Ensure emp
*/;
void glibc_slist_clean_free(struct list *x)
/*@ low_level_spec_aux
    With {B} (cont: (unit) -> program unit B) X l1
    Require safeExec(ATrue, bind(glibc_slist_clean_free_M(l1), cont), X) && sll(x, l1)
    Ensure safeExec(ATrue, bind(return(tt), cont), X) && emp
 */;
struct list *list_tail(struct list *x)
/*@ low_level_spec_aux
    With {B} (cont: (list Z * Z) -> program unit B) X l1
    Require safeExec(ATrue, bind(list_tail_M(l1), cont), X) && x != 0 && sll(x, l1)
    Ensure exists l2 v, safeExec(ATrue, bind(return(maketuple(l2,v)), cont), X) && __return != 0 && store(&(__return->next), struct list *, 0) * store(&(__return->data), int, v) * sllseg(x, __return, l2)
 */;
struct list *list_append_raw(struct list *x, struct list *y)
/*@ low_level_spec_aux
    With {B} (cont: (list Z) -> program unit B) X l1 l2
    Require safeExec(ATrue, bind(list_append_raw_M(l1, l2), cont), X) && sll(x, l1) * sll(y, l2)
    Ensure exists l3, safeExec(ATrue, bind(return(l3), cont), X) && sll(__return, l3)
 */;
