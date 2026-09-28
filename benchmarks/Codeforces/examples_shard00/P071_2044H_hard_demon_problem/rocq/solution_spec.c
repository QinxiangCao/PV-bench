/* Codeforces 2044/H - Hard Demon Problem */
// #include <stdio.h>
// #include <stdlib.h>
typedef unsigned long size_t;

/* QCP needs explicit allocator contracts because the standard-library header is
 * intentionally unavailable to the symbolic-execution front end. */
void *calloc(size_t nmemb, size_t size)
/*@ calloc_int64
    With (cap : Z)
    Require
      0 <= cap &&
      nmemb == cap &&
      size == sizeof(long long)
    Ensure
      __return != 0 &&
      Int64Array::full(__return, cap, repeat_Z(0, cap))
*/;

void free(void *ptr)
/*@ free_int64
    Require exists values cap,
      Int64Array::full(ptr, cap, values)
    Ensure emp
*/;

/*@ Extern Coq
      (zquad_1 : Z * Z * Z * Z -> Z)
      (zquad_2 : Z * Z * Z * Z -> Z)
      (zquad_3 : Z * Z * Z * Z -> Z)
      (zquad_4 : Z * Z * Z * Z -> Z)
      (RectLookup : list Z -> Z -> Z -> Z -> Z -> Z -> Z)
      (RectanglesBounded : list Z -> Z -> Z -> Prop)
      (RectIntermediatesSafe : list Z -> Z -> Prop)
      (MatrixValuesBounded : list Z -> Z -> Prop)
      (QueriesBounded : list (Z * Z * Z * Z) -> Z -> Prop)
      (RawQueriesEncode : list (Z * Z * Z * Z) -> list Z -> Prop)
      (PrefixTables : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (TablesReady : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (QueryArithmeticSafe : list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (OutputPrefix : list Z -> Z -> list (Z * Z * Z * Z) -> list Z -> Z -> Prop)
      (Spec : list Z -> Z -> list (Z * Z * Z * Z) -> list Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_full : Z -> Z -> Assertion)
      (Int64Array::seg : Z -> Z -> Z -> list Z -> Assertion)
      (Int64Array::undef_seg : Z -> Z -> Z -> Assertion)
*/

static long long rect(const long long *p, int stride, int x1, int y1, int x2, int y2)

{
    
    return p[x2 * stride + y2] - p[(x1 - 1) * stride + y2] - p[x2 * stride + y1 - 1] +
           p[(x1 - 1) * stride + y1 - 1];
}
static void solver(int n, const long long *matrix, int q, const int *queries,
                   long long *out) 
/*@ With (matrix_data : list Z)
             (queries_data : list (Z * Z * Z * Z))
             (raw_queries : list Z)
    Require
      1 <= n && n <= 2000 &&
      Zlength(matrix_data) == n * n &&
      MatrixValuesBounded(matrix_data, n) &&
      1 <= Zlength(queries_data) && Zlength(queries_data) <= 1000000 &&
      QueriesBounded(queries_data, n) &&
      (forall i, (0 <= i && i < Zlength(queries_data)) =>
        ((0 <= zquad_1(queries_data[i]) &&
          zquad_1(queries_data[i]) <= zquad_3(queries_data[i])) &&
         zquad_3(queries_data[i]) < n &&
         (0 <= zquad_2(queries_data[i]) &&
          zquad_2(queries_data[i]) <= zquad_4(queries_data[i])) &&
         zquad_4(queries_data[i]) < n)) &&
      q == Zlength(queries_data) &&
      RawQueriesEncode(queries_data, raw_queries) &&
      Int64Array::full(matrix, n * n, matrix_data) *
      IntArray::full(queries, 4 * q, raw_queries) *
      Int64Array::undef_full(out, q)
    Ensure
      exists result,
        Spec(matrix_data, n, queries_data, result) &&
        Int64Array::full(matrix, n * n, matrix_data) *
        IntArray::full(queries, 4 * q, raw_queries) *
        Int64Array::full(out, q, result)
*/
{
    int S = n + 1;
    size_t cells = (size_t)S * S;
    long long *sum = calloc(cells, sizeof(*sum))
        ;
    long long *row = calloc(cells, sizeof(*row))
        ;
    long long *col = calloc(cells, sizeof(*col))
        ;
    
    for (int i = 1; i <= n; ++i)
        
        for (int j = 1; j <= n; ++j)
        {
            
            long long x = matrix[(i - 1) * n + j - 1];
            size_t z = (size_t)i * S + j;
            
            sum[z] = x + sum[z - S] + sum[z - 1] - sum[z - S - 1];
            row[z] = x * i + row[z - S] + row[z - 1] - row[z - S - 1];
            col[z] = x * j + col[z - S] + col[z - 1] - col[z - S - 1];
        }

    for (int i = 0; i < q; ++i)
    {
        int x1 = queries[4 * i], y1 = queries[4 * i + 1], x2 = queries[4 * i + 2],
            y2 = queries[4 * i + 3];
        
        long long sm = rect(sum, S, x1, y1, x2, y2)
                      ,
                  rs = rect(row, S, x1, y1, x2, y2)
                      ,
                  cs = rect(col, S, x1, y1, x2, y2)
                      ,
                  w = y2 - y1 + 1;
        out[i] = w * (rs - (long long)x1 * sm) + cs - (long long)(y1 - 1) * sm;
    }
    free(sum);
    free(row);
    free(col);
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         int n, q;
//         scanf("%d %d", &n, &q);
//         long long *matrix = malloc((size_t)n * n * sizeof(*matrix)),
//                   *out = malloc((size_t)q * sizeof(*out));
//         int *queries = malloc((size_t)4 * q * sizeof(*queries));
//         for (int i = 0; i < n * n; ++i)
//             scanf("%lld", &matrix[i]);
//         for (int i = 0; i < 4 * q; ++i)
//             scanf("%d", &queries[i]);
//         solver(n, matrix, q, queries, out);
//         for (int i = 0; i < q; ++i)
//             printf("%lld%c", out[i], i + 1 == q ? '\n' : ' ');
//         free(matrix);
//         free(queries);
//         free(out);
//     }
//     return 0;
// }
