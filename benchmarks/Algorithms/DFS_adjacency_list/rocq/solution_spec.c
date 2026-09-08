#include "sll_def.h"

/*@ Import Coq Require Import PVbench.Algorithms.DFS_adjacency_list.rocq.spec_lib */
/*@ Import Coq Import ZSimpleGraph */

/*@ Extern Coq (G :: *) */
/*@ Extern Coq
      (DFSAdjacencyList::is_reachable : G -> Z -> Z -> Prop)
      (DFSAdjacencyList::empty_visited :
        (Z -> Prop) -> Prop)
      (ZSimpleGraph::vertex_count : G -> Z)
      (ZSimpleGraph::vertex_valid : G -> Z -> Prop)
      (DFSAdjacencyList::graph : Z -> G -> Assertion)
      (DFSAdjacencyList::visited : Z -> G -> (Z -> Prop) -> Assertion)
 */

/*
 * Recursive depth-first search over a linked-list adjacency graph.
 *
 * Vertices are numbered from 0 through vertex_count - 1.  For every vertex
 * u, adjacency[u] is the head of a linked list whose data fields contain u's
 * neighbor vertex numbers.  The graph storage is read-only; visited is
 * supplied by the caller and is updated in place.
 */
void dfs_adjacency_list(struct list **adjacency, int vertex_count,
                        int *visited, int vertex)
/*@ With (g: G) (initial_visited_set: Z -> Prop)
    Require
      vertex_count == ZSimpleGraph::vertex_count(g) &&
      0 < vertex_count && vertex_count < INT_MAX &&
      ZSimpleGraph::vertex_valid(g, vertex) &&
      DFSAdjacencyList::empty_visited(initial_visited_set) &&
      DFSAdjacencyList::graph(adjacency, g) *
      DFSAdjacencyList::visited(visited, g, initial_visited_set)
    Ensure
      exists (high_visited_set: Z -> Prop),
        (forall (v: Z),
          high_visited_set(v) => DFSAdjacencyList::is_reachable(g, vertex, v)) &&
        (forall (v: Z),
          DFSAdjacencyList::is_reachable(g, vertex, v) => high_visited_set(v)) &&
        DFSAdjacencyList::graph(adjacency, g) *
        DFSAdjacencyList::visited(visited, g, high_visited_set)
 */
{
    visited[vertex] = 1;
    struct list *edge = adjacency[vertex];
    while (edge != (struct list *)0) {
        int neighbor = edge->data;
        if (visited[neighbor] == 0) {
            dfs_adjacency_list(adjacency, vertex_count, visited, neighbor);
        } else {
        }
        edge = edge->next;
    }
}
