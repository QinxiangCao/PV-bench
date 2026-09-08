/*
 * Recursive depth-first search over an adjacency-matrix graph.
 *
 * Vertices are numbered from 0 through vertex_count - 1.  The matrix is a
 * vertex_count-by-vertex_count integer array stored in row-major order.  A
 * nonzero entry at (u, v) denotes an edge from u to v.  The matrix is
 * read-only; visited is supplied by the caller and is updated in place.
 */

void dfs_adjacency_matrix(int *matrix, int vertex_count,
                          int *visited, int vertex)

{

    visited[vertex] = 1;

    for (int neighbor = 0; neighbor < vertex_count; ++neighbor) {
        if (matrix[vertex * vertex_count + neighbor] != 0 &&
            visited[neighbor] == 0) {
            dfs_adjacency_matrix(matrix, vertex_count, visited, neighbor);
        }

    }

}
