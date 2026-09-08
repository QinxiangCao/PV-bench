int* malloc_int_array(int n)

;

void *malloc(unsigned int size)
;

void free_int_array(int *a)

;

int** prim_adjacency_matrix_return_matrix(int n, int** graph)

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
