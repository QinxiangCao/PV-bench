#include "sll_def.h"

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
