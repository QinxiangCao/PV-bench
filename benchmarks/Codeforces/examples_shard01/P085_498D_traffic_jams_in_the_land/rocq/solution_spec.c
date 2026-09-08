/*
 * Codeforces 498/D - Traffic Jams in the Land  (rating 2400, SEGMENT TREE)
 *
 * Every period divides 60 = lcm(2..6), so a segment's behaviour is fully
 * described by the 60 travel times, one per arrival time modulo 60.  Each node
 * stores that table; merging is f(r) = fl(r) + fr((r + fl(r)) mod 60), and a
 * point update rebuilds one leaf and its ancestors.
 *
 * The input is a single instance holding q queries, so solver() builds the tree
 * and answers all of them; main() only reads and prints.
 */

// #include <stdio.h>
#include "array2_ext_def.h"

/*@ Import Coq Require Import PVbench.Codeforces.examples_shard01.P085_498D_traffic_jams_in_the_land.rocq.spec_lib */
/*@ Extern Coq
      (pair : {A} {B} -> A -> B -> A * B)
      (Spec : list Z -> list (Z * Z * Z) -> list Z -> Prop)
*/


#define MAXN 100005
#define MAXQ 100005
#define P 60

/* file-scope work arrays, rebuilt on every call */
static int seg[4 * MAXN][P];
static int a_[MAXN];                      /* current periods */

/* pull: combine the two children of node v. */
static void pull(int v)
{
    for (int r = 0; r < P; r++) {
        int left = seg[2 * v][r];
        seg[v][r] = left + seg[2 * v + 1][(r + left) % P];
    }
}

static void build(int v, int lo, int hi)
{
    if (lo == hi) {
        for (int r = 0; r < P; r++)
            seg[v][r] = (r % a_[lo] == 0) ? 2 : 1;
        return;
    }
    int mid = (lo + hi) / 2;
    build(2 * v, lo, mid);
    build(2 * v + 1, mid + 1, hi);
    pull(v);
}

static void update(int v, int lo, int hi, int pos)
{
    if (lo == hi) {
        for (int r = 0; r < P; r++)
            seg[v][r] = (r % a_[lo] == 0) ? 2 : 1;
        return;
    }
    int mid = (lo + hi) / 2;
    if (pos <= mid)
        update(2 * v, lo, mid, pos);
    else
        update(2 * v + 1, mid + 1, hi, pos);
    pull(v);
}

/* query: time after crossing segments [ql, qr] starting at time t. */
static int query(int v, int lo, int hi, int ql, int qr, int t)
{
    if (ql <= lo && hi <= qr)
        return t + seg[v][t % P];
    int mid = (lo + hi) / 2;
    if (qr <= mid)
        return query(2 * v, lo, mid, ql, qr, t);
    if (ql > mid)
        return query(2 * v + 1, mid + 1, hi, ql, qr, t);
    int mt = query(2 * v, lo, mid, ql, qr, t);
    return query(2 * v + 1, mid + 1, hi, ql, qr, mt);
}

/* solver: reads no input.  Runs the q queries against the periods a[1..n]:
 * type[i] == 'C' sets a[x] to y, otherwise the travel time from city x to city
 * y is appended to out[].  Returns how many answers were written, and writes
 * the file-scope work arrays above. */
static int solver(int n, const int *a, int q, const char *type,
                  const int *qx, const int *qy, int *out)
/*@ With (periods : list Z) (kinds : list Z) (xs : list Z) (ys : list Z)
         (queries : list (Z * Z * Z))
    Require
      1 <= n && n <= 100000 && n == Zlength(periods) &&
      1 <= q && q <= 100000 && q == Zlength(kinds) &&
      Zlength(xs) == q && Zlength(ys) == q && Zlength(queries) == q &&
      (forall i, (0 <= i && i < n) => (2 <= periods[i] && periods[i] <= 6)) &&
      (forall i, (0 <= i && i < q) =>
        Znth(i, queries, pair(pair(0, 0), 0)) ==
          pair(pair(kinds[i], xs[i]), ys[i])) &&
      (forall i, (0 <= i && i < q) =>
        ((kinds[i] == 65 && 1 <= xs[i] && xs[i] < ys[i] && ys[i] <= n + 1) ||
         (kinds[i] == 67 && 1 <= xs[i] && xs[i] <= n &&
          2 <= ys[i] && ys[i] <= 6))) &&
      IntArray::seg(a, 1, n + 1, periods) * CharArray::full(type, q, kinds) *
      IntArray::full(qx, q, xs) * IntArray::full(qy, q, ys) *
      IntArray::undef_full(out, q) * IntArray::undef_seg(a_, 1, n + 1) *
      IntArray2::undef_full(seg, 400020, 60)
    Ensure
      exists (answers : list Z) (cells : list (list (option Z))),
        Spec(periods, queries, answers) &&
        __return == Zlength(answers) &&
        Zlength(cells) == 400020 &&
        (forall i, (0 <= i && i < 400020) =>
          Zlength(Znth(i, cells, nil)) == 60) &&
        IntArray::seg(a, 1, n + 1, periods) * CharArray::full(type, q, kinds) *
        IntArray::full(qx, q, xs) * IntArray::full(qy, q, ys) *
        IntArray::full(out, __return, answers) *
        IntArray::undef_seg(out, __return, q) *
        IntArray::seg_shape(a_, 1, n + 1) *
        IntArray2::mixed_full(seg, 400020, 60, cells)
*/
{
    for (int i = 1; i <= n; i++)
        a_[i] = a[i];
    build(1, 1, n);
    int nout = 0;
    for (int i = 0; i < q; i++) {
        if (type[i] == 'C') {
            a_[qx[i]] = qy[i];
            update(1, 1, n, qx[i]);
        } else {
            out[nout] = query(1, 1, n, qx[i], qy[i] - 1, 0);
            nout = nout + 1;
        }
    }
    return nout;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int a[MAXN];
//     for (int i = 1; i <= n; i++)
//         scanf("%d", &a[i]);
//     int q;
//     scanf("%d", &q);
//     static char type[MAXQ];
//     static int qx[MAXQ], qy[MAXQ], out[MAXQ];
//     for (int i = 0; i < q; i++) {
//         char c[4];
//         scanf("%1s %d %d", c, &qx[i], &qy[i]);
//         type[i] = c[0];
//     }
//     int nout = solver(n, a, q, type, qx, qy, out);
//     for (int i = 0; i < nout; i++)
//         printf("%d\n", out[i]);
//     return 0;
// }
