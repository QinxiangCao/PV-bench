#include "array2_def.h"
#include "graph_matrix_def.h"

/*
 * Recursive depth-first search over an adjacency-matrix graph.
 *
 * Vertices are numbered from 0 through vertex_count - 1.  The matrix is a
 * vertex_count-by-vertex_count integer array stored in row-major order.  A
 * nonzero entry at (u, v) denotes an edge from u to v.  The matrix is
 * read-only; visited is supplied by the caller and is updated in place.
 */

/*@ Import Coq Require Import PVbench.Algorithms.DFS_adjacency_matrix.rocq.spec_lib */
/*@ Import Coq Import ZSimpleGraph */
/*@ Extern Coq (G :: *) */
/*@ Extern Coq
      (eq :
        {A} -> A -> A -> Prop)
      (DFSAdjacencyMatrix::graph_reachable :
        G -> Z -> Z -> Prop)
      (DFSAdjacencyMatrix::processed_neighbors :
        G -> Z -> Z -> (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix::visited_extension :
        (Z -> Prop) -> (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix::empty_visited :
        (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix::adjacency_matrix_model :
        G -> list (list Z) -> Prop)
      (ZSimpleGraph::vertex_count : G -> Z)
      (ZSimpleGraph::vertex_valid : G -> Z -> Prop)
      (ZSimpleGraph::graph_step : G -> Z -> Z -> Prop)
      (ZSimpleGraph::visited_values :
        G -> list Z -> (Z -> Prop) -> Prop)
      (DFSAdjacencyMatrix::visited :
        Z -> G -> (Z -> Prop) -> Assertion)
 */

void dfs_adjacency_matrix(int *matrix, int vertex_count,
                          int *visited, int vertex)
/*@ With (g: G) (initial_visited_set: Z -> Prop)
    Require
      vertex_count == ZSimpleGraph::vertex_count(g) &&
      0 < vertex_count && vertex_count * vertex_count < INT_MAX &&
      ZSimpleGraph::vertex_valid(g, vertex) &&
      DFSAdjacencyMatrix::empty_visited(initial_visited_set) &&
      exists (rows: list (list Z)),
        GraphMatrixFlat::store_graph(
          vertex_count,
          DFSAdjacencyMatrix::adjacency_matrix_model(g),
          matrix, rows) *
      DFSAdjacencyMatrix::visited(visited, g, initial_visited_set)
    Ensure
      exists (high_visited_set: Z -> Prop),
        (forall (v: Z),
          high_visited_set(v) => DFSAdjacencyMatrix::graph_reachable(g, vertex, v)) &&
        (forall (v: Z),
          DFSAdjacencyMatrix::graph_reachable(g, vertex, v) => high_visited_set(v)) &&
        exists (rows: list (list Z)),
          GraphMatrixFlat::store_graph(
            vertex_count,
            DFSAdjacencyMatrix::adjacency_matrix_model(g),
            matrix, rows) *
        DFSAdjacencyMatrix::visited(visited, g, high_visited_set)
 */
{

    visited[vertex] = 1;

    for (int neighbor = 0; neighbor < vertex_count; ++neighbor) {
        if (matrix[vertex * vertex_count + neighbor] != 0 &&
            visited[neighbor] == 0) {
            dfs_adjacency_matrix(matrix, vertex_count, visited, neighbor);
        }

    }

}
