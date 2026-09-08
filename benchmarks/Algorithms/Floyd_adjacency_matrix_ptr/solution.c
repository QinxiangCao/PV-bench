#define MAXN 10
#define INF 1000000000

int *graph_matrix_ptr_row(int **dist, int index)

;

void floyd_adjacency_matrix_ptr(int n, int **dist)

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
