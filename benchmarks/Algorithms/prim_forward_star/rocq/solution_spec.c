#include "safeexec_def.h"
/*@ Import Coq Require Import PVbench.Algorithms.prim_forward_star.rocq.spec_lib */
/*@ Import Coq Require Import ListLib.Base.Positional */
/*@ Extern Coq (St :: *) */
/*@ Extern Coq V := Z */
/*@ Extern Coq (G :: *) */
/*@ Extern Coq (Prim2: G -> program St unit) */
/*@ Extern Coq (Prim2_loop: G -> Z -> program St unit) */
/*@ Extern Coq (initSt: G -> V -> St) */
/*@ Extern Coq (initStPred: G -> V -> St -> Prop) */
/*@ Extern Coq (PrimEnv: G -> V -> Prop) */
/*@ Extern Coq (array_graph: Z -> Z -> list Z -> list Z -> list Z -> G -> Prop) */
/*@ Extern Coq (directed_array_graph: G -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (directed_array_graph_prefix: Z -> G -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (prim_state_is: St -> St -> Prop) */
/*@ Extern Coq (prim_state_graph_matches: G -> St -> Prop) */
/*@ Extern Coq (prim_result_graph_matches_array: Z -> list Z -> list Z -> list Z -> G -> G -> Prop) */
/*@ Extern Coq (prim_result_graph_matches_array_prefix: Z -> Z -> list Z -> list Z -> list Z -> G -> G -> list Z -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (first_link_matches_inserted_vertex_directed_edges: G -> Z -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (first_link_matches_vertex_directed_edges: G -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (growing_subgraph_state: G -> St -> Prop) */
/*@ Extern Coq (visited_matches_state: G -> St -> list Z -> Prop) */
/*@ Extern Coq (state_vertex_count: St -> Z) */
/*@ Extern Coq (parent_edges_match_state: G -> V -> St -> list Z -> Prop) */
/*@ Extern Coq (lowcost_parent_match: G -> St -> list Z -> list Z -> Z -> Prop) */
/*@ Extern Coq (candidate_vertex_exists_in_range: Z -> G -> St -> list Z -> list Z -> Z -> Prop) */
/*@ Extern Coq (min_vertex_in_range: G -> St -> Z -> Z -> V -> list Z -> list Z -> Prop) */
/*@ Extern Coq (selected_parent_edge_is_min_cut_edge: G -> St -> list Z -> V -> Prop) */
/*@ Extern Coq (selected_parent_pair: G -> St -> list Z -> list Z -> list Z -> V -> V -> V -> Prop) */
/*@ Extern Coq (selected_parent_add_to_mst: G -> St -> St -> list Z -> list Z -> list Z -> V -> Prop) */
/*@ Extern Coq (selected_state_after_add: G -> V -> Z -> Z -> St -> St -> list Z -> list Z -> list Z -> list Z -> list Z -> V -> Prop) */
/*@ Extern Coq (scan_minIndex_adjacency_prefix_update: G -> St -> list Z -> list Z -> list Z -> list Z -> list Z -> V -> Z -> list Z -> list Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (scan_one_directed_edge_update: G -> St -> list Z -> list Z -> list Z -> list Z -> Z -> list Z -> list Z -> Prop) */
/*@ Extern Coq (scan_minIndex_adjacency_update: G -> St -> list Z -> list Z -> list Z -> list Z -> list Z -> V -> list Z -> list Z -> list Z -> list Z -> Prop) */
struct mst_tree {
	int* u;
	int* v;
	int* wt;
};

int* malloc_int_array(int n)

;

struct mst_tree* malloc_mst_tree()

;

struct mst_tree* prim(int* from_arr, int* to_arr, int* weight_arr, int n, int m)
/*@ With (lf: list Z) (lt: list Z) (lw: list Z) (g : G) (src: V) X
		Require
			src == 0 &&
			2 <= n && n < INT_MAX &&
			1 <= m && 2 * m < INT_MAX &&
			(forall (k: Z), (0 <= k && k < m) => 0 <= Znth(k, lf, 0) && Znth(k, lf, 0) < n) &&
			(forall (k: Z), (0 <= k && k < m) => 0 <= Znth(k, lt, 0) && Znth(k, lt, 0) < n) &&
			(forall (k: Z), (0 <= k && k < m) => 0 <= Znth(k, lw, 0) && Znth(k, lw, 0) < 1000000000) &&
			array_graph(n, m, lf, lt, lw, g) &&
			PrimEnv(g, src) &&
			safeExec(initStPred(g, src), Prim2(g), X) &&

			IntArray::full(from_arr, m, lf) *
			IntArray::full(to_arr, m, lt) *
			IntArray::full(weight_arr, m, lw)
	Ensure
		exists lru lrv lrwt rg
			   r_from_new r_to_new r_weight_new r_first r_link r_lowcost r_visited r_edge_parent
			   l_from_new_ret l_to_new_ret l_weight_new_ret l_first_ret l_link_ret
			   l_lowcost_ret l_visited_ret l_edge_parent_ret,
			safeExec(prim_state_graph_matches(rg), return(tt), X) &&
			prim_result_graph_matches_array(n, lru, lrv, lrwt, g, rg) &&
			__return != 0 &&

			IntArray::full(__return -> u, n - 1, lru) *
			IntArray::full(__return -> v, n - 1, lrv) *
			IntArray::full(__return -> wt, n - 1, lrwt) *
			IntArray::full(from_arr, m, lf) *
			IntArray::full(to_arr, m, lt) *
			IntArray::full(weight_arr, m, lw) *
			IntArray::full(r_from_new, 2 * m, l_from_new_ret) *
			IntArray::full(r_to_new, 2 * m, l_to_new_ret) *
			IntArray::full(r_weight_new, 2 * m, l_weight_new_ret) *
			IntArray::full(r_first, n, l_first_ret) *
			IntArray::full(r_link, 2 * m, l_link_ret) *
			IntArray::full(r_lowcost, n, l_lowcost_ret) *
			IntArray::full(r_visited, n, l_visited_ret) *
			IntArray::full(r_edge_parent, n, l_edge_parent_ret)
*/
{
	int* out_u = malloc_int_array(n - 1);
	int* out_v = malloc_int_array(n - 1);
	int* out_wt = malloc_int_array(n - 1);

    int* from_new = malloc_int_array(2*m);
    int* to_new = malloc_int_array(2*m);
    int* weight_new = malloc_int_array(2*m);
		int i = 0;

	    for (; i < m; i++) {
        from_new[2*i] = from_arr[i];
        to_new[2*i] = to_arr[i];
        weight_new[2*i] = weight_arr[i];

        from_new[2*i + 1] = to_arr[i];
        to_new[2*i + 1] = from_arr[i];
        weight_new[2*i + 1] = weight_arr[i];
    }

		int* first = malloc_int_array(n);
		int* link = malloc_int_array(2 * m);
		 i = 0;

	for (; i < n; i++) {
		first[i] = -1;
	}

	i = 0;

		for (; i < 2 * m; i++) {
			link[i] = -1;
		}

		i = 0;

		for (; i < 2 * m; i++) {
			int u = from_new[i];

			int tmp = first[u];
			first[u] = i;
			link[i] = tmp;
		}

	int* visited = malloc_int_array(n);
		int* lowcost = malloc_int_array(n);
		int* edge_parent = malloc_int_array(n);
		i = 0;

			for (; i < n; i++) {
				lowcost[i] = 1000000000;
				visited[i] = 0;
			edge_parent[i] = -1;
		}

		lowcost[0] = 0;
		i = 0;

					for (; i < n; i++) {
						int min = 1000000000;
						int minIndex = -1;
					int j =0;

					for (; j < n; j++) {
					if (visited[j] == 0) {
						if (lowcost[j] < min) {
							min = lowcost[j];
							minIndex = j;
						}
					}
				    }

					if (minIndex != -1) {
						visited[minIndex] = 1;

							int cur_edge = first[minIndex];

						while (cur_edge != -1) {
								if (0 <= cur_edge && cur_edge < 2 * m) {
										int to_node = to_new[cur_edge];
										int edge_weight = weight_new[cur_edge];

													if (0 <= to_node && to_node < n && visited[to_node] == 0 && edge_weight < lowcost[to_node])
											 {
									lowcost[to_node] = edge_weight;
									edge_parent[to_node] = cur_edge;
												}

								cur_edge = link[cur_edge];

					} else {
						cur_edge = -1;
					}
				}

			}
	}

	i = 1;
	int mst_idx = 0;

	for (; i < n; i++) {
		if (edge_parent[i] == -1) continue;
		int edge_id = edge_parent[i];
		if (0 <= edge_id && edge_id < 2 * m && mst_idx < n - 1) {
			out_u[mst_idx] = from_new[edge_id];
			out_v[mst_idx] = to_new[edge_id];
			out_wt[mst_idx] = weight_new[edge_id];
			mst_idx++;
		}
	}

	struct mst_tree* p = malloc_mst_tree();
	p->u = out_u;
	p->v = out_v;
	p->wt = out_wt;
	return p;
}
