#include "int_ptr_array2_def.h"

/*
 * Recursive depth-first search over an adjacency-matrix graph.
 *
 * Vertices are numbered from 0 through vertex_count - 1.  The matrix is a
 * vertex_count-by-vertex_count integer pointer array.  A nonzero entry at
 * matrix[u][v] denotes an edge from u to v.  The matrix is read-only; visited
 * is supplied by the caller and is updated in place.
 */

/*@ Import Coq Require Import PVbench.Algorithms.DFS_adjacency_matrix_2Darray.rocq.spec_lib */
/*@ Import Coq Import ZSimpleGraph */
/*@ Extern Coq (G :: *) */
/*@ Extern Coq
      (eq :
        {A} -> A -> A -> Prop)
      (DFSAdjacencyMatrix2Darray::graph_reachable :
        G -> Z -> Z -> Prop)
      (DFSAdjacencyMatrix2Darray::processed_neighbors :
        G -> Z -> Z -> (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix2Darray::visited_extension :
        (Z -> Prop) -> (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix2Darray::empty_visited :
        (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix2Darray::adjacency_matrix_model :
        G -> list (list Z) -> Prop)
      (ZSimpleGraph::vertex_count : G -> Z)
      (ZSimpleGraph::vertex_valid : G -> Z -> Prop)
      (ZSimpleGraph::graph_step : G -> Z -> Z -> Prop)
      (ZSimpleGraph::visited_values :
        G -> list Z -> (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix2Darray::store_graph :
        Z -> G -> list (list Z) -> Assertion)
      (DFSAdjacencyMatrix2Darray::graph : Z -> G -> Assertion)
      (DFSAdjacencyMatrix2Darray::visited :
        Z -> G -> (Z -> Prop) -> Assertion)
 */

void dfs_adjacency_matrix_2Darray(int **matrix, int vertex_count,
                                  int *visited, int vertex)
/*@ With (g: G) (initial_visited_set: Z -> Prop)
    Require
      vertex_count == ZSimpleGraph::vertex_count(g) &&
      0 < vertex_count && vertex_count < INT_MAX &&
      ZSimpleGraph::vertex_valid(g, vertex) &&
      DFSAdjacencyMatrix2Darray::empty_visited(initial_visited_set) &&
      DFSAdjacencyMatrix2Darray::graph(matrix, g) *
      DFSAdjacencyMatrix2Darray::visited(visited, g, initial_visited_set)
    Ensure
      exists (high_visited_set: Z -> Prop),
        (forall (v: Z),
          high_visited_set(v) =>
            DFSAdjacencyMatrix2Darray::graph_reachable(g, vertex, v)) &&
        (forall (v: Z),
          DFSAdjacencyMatrix2Darray::graph_reachable(g, vertex, v) =>
            high_visited_set(v)) &&
        DFSAdjacencyMatrix2Darray::graph(matrix, g) *
        DFSAdjacencyMatrix2Darray::visited(visited, g, high_visited_set)
 */
{

    visited[vertex] = 1;

    for (int neighbor = 0; neighbor < vertex_count; ++neighbor) {

        int edge_exists = matrix[vertex][neighbor];

        if (edge_exists != 0 && visited[neighbor] == 0) {
            dfs_adjacency_matrix_2Darray(matrix, vertex_count, visited, neighbor);
        }

    }

}
