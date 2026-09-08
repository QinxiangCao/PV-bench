#include "array2_def.h"
#include "graph_matrix_def.h"

/*@ Import Coq Require Import PVbench.Algorithms.Floyd_adjacency_matrix_2Darray.rocq.spec_lib */
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

void floyd_adjacency_matrix_2Darray(int n, int dist[MAXN][MAXN])
/*@ With (g: G) (dist0: list (list Z))
    Require
      FloydAdjacencyMatrix2Darray::graph_has_size(g, n) &&
      FloydAdjacencyMatrix2Darray::floyd_init_matrix(g, dist0) &&
      GraphMatrixFlat::store_graph(
        MAXN,
        FloydAdjacencyMatrix2Darray::graph_matrix_model(g),
        dist, dist0)
    Ensure
      exists (dist1: list (list Z)),
        FloydAdjacencyMatrix2Darray::floyd_shortest_matrix(g, dist1) &&
        GraphMatrixFlat::store_graph(
          MAXN,
          FloydAdjacencyMatrix2Darray::matrix_rows_model,
          dist, dist1)
 */
{

    int k, i, j;

    for (k = 0; k < n; ++k) {

        for (i = 0; i < n; ++i) {

            for (j = 0; j < n; ++j) {

                if (dist[i][k] < INF &&
                    dist[k][j] < INF &&
                    dist[i][k] + dist[k][j] < dist[i][j]) {
                    dist[i][j] = dist[i][k] + dist[k][j];
                }
            }
        }
    }
}
