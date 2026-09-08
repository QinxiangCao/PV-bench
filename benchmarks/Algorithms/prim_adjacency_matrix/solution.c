int* malloc_int_array(int n)

;

void free_int_array(int *a)

;

long long prim_adjacency_matrix(int n, int** graph)

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
                        }
                    }
                }
            }

        }

	    }
	    long long ret = 0;
	    i = 0;

    for (; i < n; i++) {
        ret += lowcost[i];
    }

    free_int_array(visited) ;
    free_int_array(lowcost) ;
    return ret;
}
