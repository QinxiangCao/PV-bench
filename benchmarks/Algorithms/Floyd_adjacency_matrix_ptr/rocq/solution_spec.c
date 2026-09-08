#include "graph_matrix_def.h"

/*@ Import Coq Require Import PVbench.Algorithms.Floyd_adjacency_matrix_ptr.rocq.spec_lib */
/*@ Import Coq Import FloydGraph */
/*@ Import Coq Import FloydAdjacencyMatrix2Darray */
/*@ Extern Coq (G :: *) */
/*@ Extern Coq (state :: *) */
/*@ Extern Coq
      (FloydAdjacencyMatrix2Darray::state_of_matrix:
        list (list Z) -> state)
      (FloydAdjacencyMatrix2Darray::state_model:
        list (list Z) -> state -> Prop)
      (FloydAdjacencyMatrix2Darray::graph_storage_size:
        G -> Z)
      (FloydAdjacencyMatrix2Darray::graph_matrix_model:
        G -> list (list Z) -> Prop)
      (FloydAdjacencyMatrix2Darray::matrix_storage_size:
        Z)
      (FloydAdjacencyMatrix2Darray::matrix_rows_model:
        list (list Z) -> Prop)
      (FloydAdjacencyMatrix2Darray::graph_has_size:
        G -> Z -> Prop)
      (FloydAdjacencyMatrix2Darray::matrix_shape:
        list (list Z) -> Prop)
      (FloydAdjacencyMatrix2Darray::matrix_values_safe:
        list (list Z) -> Prop)
      (FloydAdjacencyMatrix2Darray::floyd_init_matrix:
        G -> list (list Z) -> Prop)
      (FloydAdjacencyMatrix2Darray::floyd_shortest_matrix:
        G -> list (list Z) -> Prop)
      (eq: {A} -> A -> A -> Prop)
*/
#define MAXN 10
#define INF 1000000000

int *graph_matrix_ptr_row(int **dist, int index)

;

void floyd_adjacency_matrix_ptr(int n, int **dist)
/*@ With (g: G) (dist0: list (list Z))
    Require
      FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
      FloydAdjacencyMatrix2Darray::floyd_init_matrix(g, dist0) &&
      GraphMatrixPtr::store_graph(
        MAXN,
        FloydAdjacencyMatrix2Darray::graph_matrix_model(g),
        dist, dist0)
    Ensure
      exists (dist1: list (list Z)),
        FloydAdjacencyMatrix2Darray::floyd_shortest_matrix(g, dist1) &&
        GraphMatrixPtr::store_graph(
          MAXN,
          FloydAdjacencyMatrix2Darray::matrix_rows_model,
          dist, dist1)
 */
{

    int k, i, j;

    for (k = 0; k < n; ++k) {

        for (i = 0; i < n; ++i) {

            for (j = 0; j < n; ++j) {
                int *row_k;
                int *row_i;
                int dkj;
                int dik;
                int dij;

                row_k = graph_matrix_ptr_row(dist, k);

                dkj = row_k[j];

                row_i = graph_matrix_ptr_row(dist, i);

                dik = row_i[k];

                row_i = graph_matrix_ptr_row(dist, i);

                dij = row_i[j];

                if (dik < INF && dkj < INF && dik + dkj < dij) {
                    row_i = graph_matrix_ptr_row(dist, i);

                    row_i[j] = dik + dkj;
                }
            }
        }
    }
}
