#include "Data_structures/union_find/union_find_def.h"

int* malloc_int_array(int n)

;
/*@ Extern Coq (G :: *) */
/*@ Extern Coq (KruskalEnv : G -> Prop) */
/*@ Extern Coq (Zrange : Z -> Z -> list Z) */
/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (array_graph : Z -> Z -> list Z -> list Z -> list Z -> G -> Prop) */
/*@ Extern Coq (edge_arrays_ordered_by : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (after_sorted_edge_of_input : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (same_outside_edge_arrays_range : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop) */
/*@ Extern Coq (edge_arrays_partitioned_by_weight_at : list Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (edge_arrays_range_sorted_by_weight : list Z -> Z -> Z -> Prop) */
/*@ Extern Coq (St :: *) */
/*@ Extern Coq (kruskal_scan_state : G -> list Z -> Z -> Z -> St -> Prop) */
/*@ Extern Coq (kruskal_scan_phase : G -> St -> Z -> Prop) */
/*@ Extern Coq (output_prefix_matches_state : G -> Z -> list Z -> list Z -> list Z -> St -> Prop) */
/*@ Extern Coq (initStPred : G -> St -> Prop) */
/*@ Extern Coq (kruskal_state_is : St -> St -> Prop) */
/*@ Extern Coq (kruskal_state_graph_matches : G -> St -> Prop) */
/*@ Extern Coq (union_find_connectivity_matches_state : G -> St -> (Z -> Z) -> Prop) */
/*@ Extern Coq (selected_edge_is_min_edge : G -> list Z -> Z -> St -> Z -> Prop) */
/*@ Extern Coq (selected_edge_pair : G -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (selected_edge_add_to_mst : St -> St -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (return_is_mst : G -> G -> Prop) */
/*@ Extern Coq (kruskal_result_graph_matches_array : list Z -> list Z -> list Z -> G -> G -> Prop) */
/*@ Import Coq Local Open Scope monad */
/*@ Import Coq Require Import PVbench.Algorithms.kruskal_union_find.rocq.spec_lib */
/*@ Import Coq Require Import ListLib.Base.Positional */
/*@ Import Coq From SumLib Require Import ZRange */
void free_int_array(int* a)

;

struct mst_tree {
	int* ru;
	int* rv;
	int* rw;
};

struct mst_tree* malloc_mst_tree()

;

void swap_int(int* a, int* b)

{
	int t = *a;
	*a = *b;
	*b = t;
}

void swap_edge(int* u, int* v, int* w, int i, int j)

{
	if (i != j) {
		if (i < j) {

			swap_int(&u[i], &u[j]) ;
			swap_int(&v[i], &v[j]) ;
			swap_int(&w[i], &w[j]) ;
		} else {

			swap_int(&u[i], &u[j]) ;
			swap_int(&v[i], &v[j]) ;
			swap_int(&w[i], &w[j]) ;
		}
	}
}

int partitionByWeight(int* u, int* v, int* w, int left, int right)

{
	int pivot_w = w[right];
	int i = left;

	for (int j = left; j < right; j++) {
		if (w[j] < pivot_w) {
			swap_edge(u, v, w, i, j)
				;
			i++;
		}
	}

	swap_edge(u, v, w, i, right)
		;
	return i;
}

void quickByWeightRange(int* u, int* v, int* w, int left, int right)

{
	if (left < right) {
		int pivot = partitionByWeight(u, v, w, left, right);
		quickByWeightRange(u, v, w, left, pivot - 1);
		quickByWeightRange(u, v, w, pivot + 1, right);
	}
}

void quickByWeight(int* u, int* v, int* w, int n)

{
	if (n > 0) {
		quickByWeightRange(u, v, w, 0, n - 1);
	}
}

struct mst_tree* kruskal(int*u, int* v, int* w, int n, int m)
/*@ With orig_u orig_v orig_w (g : G)
		Require 2 <= n && n < INT_MAX &&
				1 <= m && m < INT_MAX &&
				array_graph(n, m, orig_u, orig_v, orig_w, g) &&
				KruskalEnv(g) &&
				edge_arrays_ordered_by(m, orig_u, orig_v, orig_w,
				orig_u, orig_v, orig_w, Zrange(0, m)) &&
			IntArray::full(u, m, orig_u) *
			IntArray::full(v, m, orig_v) *
			IntArray::full(w, m, orig_w)
		Ensure exists l_u l_v l_w edge_order lru lrv lrw rg,
				return_is_mst(g, rg) &&
				after_sorted_edge_of_input(m, orig_u, orig_v, orig_w,
					l_u, l_v, l_w, edge_order) &&
				kruskal_result_graph_matches_array(lru, lrv, lrw, g, rg) &&
				__return != 0 &&
				IntArray::full(u, m, l_u) *
				IntArray::full(v, m, l_v) *
				IntArray::full(w, m, l_w) *
				IntArray::full(__return -> ru, n - 1, lru) *
			IntArray::full(__return -> rv, n - 1, lrv) *
			IntArray::full(__return -> rw, n - 1, lrw)
*/
{
	quickByWeight(u, v, w, m)
		;

	struct union_find* uf = uf_create(n);

	int* out_u = malloc_int_array(n - 1);
	int* out_v = malloc_int_array(n - 1);
	int* out_w = malloc_int_array(n - 1);

	int chosen = 0;
	int i = 0;

	for (; i < m && chosen < n - 1; i++) {
		int edge_u = u[i];
		int edge_v = v[i];
		int edge_w = w[i];

		int root_u = uf_find(uf, edge_u)
			;

		int root_v = uf_find(uf, edge_v)
			;

		if (root_u != root_v) {
			out_u[chosen] = edge_u;
			out_v[chosen] = edge_v;
			out_w[chosen] = edge_w;
			chosen++;
			uf_union(uf, edge_u, edge_v)
				;

		} else {

		}

		}

	uf_free(uf) ;

	struct mst_tree* result = malloc_mst_tree();
	result->ru = out_u;
	result->rv = out_v;
	result->rw = out_w;
	return result;

}
