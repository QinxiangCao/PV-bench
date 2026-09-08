#define MAXN 10
#define INF 1000000000

void floyd_adjacency_matrix_2Darray(int n, int dist[MAXN][MAXN])

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
