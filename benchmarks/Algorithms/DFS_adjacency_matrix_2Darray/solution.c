/*
 * Recursive depth-first search over an adjacency-matrix graph.
 *
 * Vertices are numbered from 0 through vertex_count - 1.  The matrix is a
 * vertex_count-by-vertex_count integer pointer array.  A nonzero entry at
 * matrix[u][v] denotes an edge from u to v.  The matrix is read-only; visited
 * is supplied by the caller and is updated in place.
 */

void dfs_adjacency_matrix_2Darray(int **matrix, int vertex_count,
                                  int *visited, int vertex)

{

    visited[vertex] = 1;

    for (int neighbor = 0; neighbor < vertex_count; ++neighbor) {

        int edge_exists = matrix[vertex][neighbor];

        if (edge_exists != 0 && visited[neighbor] == 0) {
            dfs_adjacency_matrix_2Darray(matrix, vertex_count, visited, neighbor);
        }

    }

}
