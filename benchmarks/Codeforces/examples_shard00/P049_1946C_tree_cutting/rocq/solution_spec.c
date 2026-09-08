/* Codeforces 1946/C - Tree Cutting */
// #include <stdio.h>
// #include <stdlib.h>

static int n, k, *head, *to, *next_edge, *parent, *order, *size_sub;

/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Pre : Z -> Z -> list (Z*Z) -> Prop)
      (Spec : Z -> Z -> list (Z*Z) -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (IntArray::seg_shape : Z -> Z -> Z -> Assertion)
      (IntArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
      (IntArray::mixed_missing_i : Z -> Z -> Z -> Z -> list (option Z) -> Assertion)
      (FreshSizeCells : Z -> list (option Z) -> Prop)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P049_1946C_tree_cutting.rocq.spec_lib */

/* QCP uses one named contract at each allocation site.  Keeping the six
 * contracts distinct makes the ownership introduced at each global pointer
 * assignment explicit. */
void *malloc(unsigned long size)
/*@ malloc_head
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::undef_full(__return, cap)
*/
/*@ malloc_to
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::undef_full(__return, cap)
*/
/*@ malloc_next_edge
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::undef_full(__return, cap)
*/
/*@ malloc_parent
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::undef_full(__return, cap)
*/
/*@ malloc_order
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::undef_full(__return, cap)
*/
/*@ malloc_size_sub
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure exists cells,
           __return != 0 && FreshSizeCells(cap, cells) &&
           Zlength(cells) == cap &&
           IntArray::mixed_full(__return, cap, cells)
*/;

void free(void *ptr)
/*@ free_head
    With (cap : Z) (values : list Z)
    Require 0 <= cap && Zlength(values) == cap && IntArray::full(ptr, cap, values)
    Ensure emp
*/
/*@ free_to
    With (cap : Z) (values : list Z)
    Require 0 <= cap && Zlength(values) == cap && IntArray::full(ptr, cap, values)
    Ensure emp
*/
/*@ free_next_edge
    With (cap : Z) (values : list Z)
    Require 0 <= cap && Zlength(values) == cap && IntArray::full(ptr, cap, values)
    Ensure emp
*/
/*@ free_parent
    With (cap : Z) (values : list Z)
    Require 0 <= cap && Zlength(values) == cap && IntArray::full(ptr, cap, values)
    Ensure emp
*/
/*@ free_order
    With (cap : Z) (values : list Z)
    Require 0 <= cap && Zlength(values) == cap && IntArray::full(ptr, cap, values)
    Ensure emp
*/
/*@ free_size_sub
    With (cap : Z)
    Require 0 <= cap && IntArray::undef_full(ptr, cap)
    Ensure emp
*/;

static int feasible(int minimum)

{
    
    for (int i = 0; i < n; ++i)
        size_sub[i] = 1;

    int components = 0;
    
    for (int oi = n - 1; oi >= 0; --oi) {
        int v = order[oi];
        if (size_sub[v] >= minimum) {
            ++components;
            size_sub[v] = 0;
        }
        if (parent[v] >= 0)
            size_sub[parent[v]] += size_sub[v];
    }

    return components >= k + 1;
}

static int solver(int nn, int kk, const int *eu, const int *ev)

/*@ With (nv : Z)
             (kv : Z)
             (edges : list (Z*Z))
             (eu_data ev_data : list Z)
             (n_before k_before : Z)
             (head_before to_before next_before : Z)
             (parent_before order_before size_before : Z)
    Require
      1 <= kv && kv < nv &&
      nv <= 100000 &&
      Zlength(edges)==nv-1 &&
      (forall i, (0 <= i && i < Zlength(edges)) => ((1 <= fst(edges[i]) && fst(edges[i]) <= nv) && (1 <= snd(edges[i]) && snd(edges[i]) <= nv))) &&
      Pre(nv, kv, edges) &&
      nn == nv && kk == kv &&
      Zlength(eu_data) == Zlength(edges) && Zlength(ev_data) == Zlength(edges) &&
      (forall i, (0 <= i && i < Zlength(edges)) =>
        (eu_data[i] == fst(edges[i]) - 1 && ev_data[i] == snd(edges[i]) - 1)) &&
      IntArray::full(eu, Zlength(edges), eu_data) *
      IntArray::full(ev, Zlength(edges), ev_data) *
      store(&n, int, n_before) * store(&k, int, k_before) *
      store(&head, int *, head_before) * store(&to, int *, to_before) *
      store(&next_edge, int *, next_before) *
      store(&parent, int *, parent_before) * store(&order, int *, order_before) *
      store(&size_sub, int *, size_before)
    Ensure
      exists head_after to_after next_after parent_after order_after size_after,
      Spec(nv, kv, edges, __return) &&
      eu == eu@pre && ev == ev@pre &&
      IntArray::full(eu, Zlength(edges), eu_data) *
      IntArray::full(ev, Zlength(edges), ev_data) *
      store(&n, int, nv) * store(&k, int, kv) *
      store(&head, int *, head_after) * store(&to, int *, to_after) *
      store(&next_edge, int *, next_after) *
      store(&parent, int *, parent_after) *
      store(&order, int *, order_after) *
      store(&size_sub, int *, size_after)
*/

{
    n = nn;
    k = kk;

    head = malloc(n * sizeof(*head))
      ;
    to = malloc((2 * n - 2) * sizeof(*to))
      ;
    next_edge = malloc((2 * n - 2) * sizeof(*next_edge))
      ;

    for (int i = 0; i < n; ++i)
        head[i] = -1;

    int ec = 0;
    
    for (int i = 0; i + 1 < n; ++i) {
        int u = eu[i], v = ev[i];

        to[ec] = v;
        next_edge[ec] = head[u];
        head[u] = ec;
        ec++;

        to[ec] = u;
        next_edge[ec] = head[v];
        head[v] = ec;
        ec++;
    }

    parent = malloc(n * sizeof(*parent))
      ;
    order = malloc(n * sizeof(*order))
      ;
    size_sub = malloc(n * sizeof(*size_sub))
      ;

    int top = 1;
    order[0] = 0;
    parent[0] = -1;

    for (int i = 0; i < top; ++i) {
        int v = order[i];
        
        int traversal_parent = parent[v];
        
        for (int e = head[v]; e != -1; e = next_edge[e])
            if (to[e] != traversal_parent) {
                
                parent[to[e]] = v;
                order[top] = to[e];
                top++;
            }
    }

    int lo = 1;
    int hi = n / (k + 1);
    int ans = 1;

    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        
        if (feasible(mid) ) {
            ans = mid;
            lo = mid + 1;
        } else
            hi = mid - 1;
    }

    free(head) ;
    free(to) ;
    free(next_edge) ;
    free(parent) ;
    free(order) ;
    free(size_sub) ;

    return ans;
}

// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--) {
//         scanf("%d %d", &n, &k);
//         int *eu = malloc((size_t)(n - 1) * sizeof(*eu)),
//             *ev = malloc((size_t)(n - 1) * sizeof(*ev));
//         for (int i = 0; i + 1 < n; ++i) {
//             scanf("%d %d", &eu[i], &ev[i]);
//             --eu[i];
//             --ev[i];
//         }
//         printf("%d\n", solver(n, k, eu, ev));
//         free(eu);
//         free(ev);
//     }
//     return 0;
// }
