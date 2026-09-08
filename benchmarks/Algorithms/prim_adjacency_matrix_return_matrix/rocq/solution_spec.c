#include "int_ptr_array2_def.h"
#include "graph_matrix_def.h"

int* malloc_int_array(int n)

;
/*@ Import Coq Require Import PVbench.Algorithms.prim_adjacency_matrix_return_matrix.rocq.spec_lib */
/*@ Import Coq Require Import ListLib.Base.Positional */
/*@ Extern Coq (St :: *) */
/*@ Extern Coq V := Z */
/*@ Extern Coq (E :: *) */
/*@ Extern Coq (G :: *) */
/*@ Extern Coq (initSt: G -> V -> St) */
/*@ Extern Coq (initStPred: G -> V -> St -> Prop) */
/*@ Extern Coq (PrimEnv: G -> V -> Prop) */
/*@ Extern Coq (prim_adjacency_matrix_graph_model: Z -> G -> Z -> list (list Z) -> Prop) */
/*@ Extern Coq (prim_result_matrix_matches: list (list Z) -> G -> Z -> Prop) */
/*@ Extern Coq (result_matrix_parent_prefix: G -> V -> list (list Z) -> list (list Z) -> list Z -> list E -> Z -> Z -> Prop) */
/*@ Extern Coq (vertex_parent_matches_edge_parent: G -> V -> list Z -> list E -> Prop) */
/*@ Extern Coq (inf_matrix: Z -> Z -> Z -> list (list Z)) */
/*@ Extern Coq (set_matrix_entry: list (list Z) -> Z -> Z -> Z -> list (list Z)) */
/*@ Extern Coq (set_undirected_matrix_entry: list (list Z) -> Z -> Z -> Z -> list (list Z)) */
/*@ Extern Coq (PtrArray::undef_full : Z -> Z -> Assertion) */
/*@ Extern Coq (PtrArray::undef_seg : Z -> Z -> Z -> Assertion) */
/*@ Extern Coq (prim_result_weight: G -> Z -> Prop) */
/*@ Extern Coq (prim_input_weight_bound: Z -> Z -> Prop) */
/*@ Extern Coq (prim_result_weight_in_int64_range: G -> Prop) */
/*@ Extern Coq (lowcost_prefix_sum: Z -> list Z -> Z) */
/*@ Extern Coq (lowcost_sum_matches_state: St -> list Z -> Prop) */
/*@ Extern Coq (lowcost_values_in_range: Z -> list Z -> Prop) */
/*@ Extern Coq (prim_state_is: St -> St -> Prop) */
/*@ Extern Coq (prim_state_graph_matches: G -> St -> Prop) */
/*@ Extern Coq (return_is_mst: G -> G -> Prop) */
/*@ Extern Coq (visited_matches_state: G -> St -> list Z -> Prop) */
/*@ Extern Coq (state_vertex_count: St -> Z) */
/*@ Extern Coq (growing_subgraph_state: G -> St -> Prop) */
/*@ Extern Coq (default_edge_list: Z -> list E) */
/*@ Extern Coq (lowcost_parent_match: G -> St -> list Z -> list E -> Z -> Prop) */
/*@ Extern Coq (selected_edges_match_state: G -> V -> St -> list E -> Prop) */
/*@ Extern Coq (candidate_vertex_exists_in_range: Z -> G -> St -> list Z -> list E -> Z -> Prop) */
/*@ Extern Coq (min_vertex_in_range: G -> St -> Z -> Z -> V -> list Z -> list E -> Prop) */
/*@ Extern Coq (selected_parent_edge_is_min_cut_edge: G -> St -> list E -> V -> Prop) */
/*@ Extern Coq (selected_parent_pair: G -> St -> list E -> V -> V -> V -> Prop) */
/*@ Extern Coq (selected_parent_add_to_mst: G -> St -> St -> list E -> V -> Prop) */
/*@ Extern Coq (scan_matrix_row_prefix_update: G -> list (list Z) -> Z -> St -> V -> Z -> list Z -> list E -> list Z -> list E -> Prop) */
/*@ Extern Coq (scan_matrix_row_full_update: Z -> G -> list (list Z) -> Z -> St -> V -> list Z -> list E -> list Z -> list E -> Prop) */
void *malloc(unsigned int size)
;

void free_int_array(int *a)

;

int** prim_adjacency_matrix_return_matrix(int n, int** graph)
/*@ With (matrix: list (list Z)) (g: G) (src: V)
	    Require
	        src == 0 &&
	        2 <= n && n < INT_MAX &&
	        n * sizeof(void *) <= UINT_MAX &&
	        prim_input_weight_bound(n, 1000000000) &&
	        PrimEnv(g, src) &&

	        GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix)
		    Ensure
		        exists rg result_matrix,
		            return_is_mst(g, rg) &&
		            prim_result_matrix_matches(result_matrix, rg, 1000000000) &&

		            GraphMatrixPtr::store_graph(n, prim_adjacency_matrix_graph_model(n, g, 1000000000), graph, matrix) *
		            IntPtrArray2::full(__return, n, result_matrix)
	*/
{
    int* visited = malloc_int_array(n);
    int i = 0;

    for (; i < n; i++) {
        visited[i] = 0;
    }

    int* lowcost = malloc_int_array(n);
    i = 0;

    for (; i < n; i++) {
        lowcost[i] = 1000000000;
    }

    int* vertex_parent = malloc_int_array(n);
    i = 0;

    for (; i < n; i++) {
        vertex_parent[i] = -1;
    }

    lowcost[0] = 0;
    i = 0;

    for (; i < n; i++) {
        int minIndex = -1;
        int min = 1000000000;
        int j = 0;

        for (; j < n; j++) {
            if (visited[j] == 0 && lowcost[j] < min)  {
                min = lowcost[j];
                minIndex = j;
            }
        }

        if (0 <= minIndex && minIndex < n) {
            visited[minIndex] = 1;

            int* selected_row = graph[minIndex];
            j = 0;

            for (; j < n; j++) {

                int w = selected_row[j];
                if (w != 1000000000) {

                    if (visited[j] == 0) {
                        if (w < lowcost[j]) {
                            lowcost[j] = w;
                            vertex_parent[j] = minIndex;
                        }
                    }
                }
            }

        }

	    }
    int** mst = (int**)malloc(sizeof(void*) * n)
      ;
    i = 0;

    for (; i < n; i++) {
        mst[i] = malloc_int_array(n);
        int j = 0;

        for (; j < n; j++) {
            mst[i][j] = 1000000000;
        }

    }

    i = 0;

    for (; i < n; i++) {
        int p = vertex_parent[i];
        if (0 <= p && p < n) {

            int w = graph[p][i];

	            mst[p][i] = w;

            mst[i][p] = w;

        }
    }

    free_int_array(visited) ;
    free_int_array(lowcost) ;
    free_int_array(vertex_parent) ;
    return mst;
}
