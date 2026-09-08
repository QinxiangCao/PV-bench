/* Codeforces 1067/B - Multihedgehog */
// #include <stdio.h>
// #include <stdlib.h>

static int n, *head, *to, *nxt, *deg;

/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Pre : Z -> Z -> list (Z * Z) -> Prop)
      (Spec : Z -> Z -> list (Z * Z) -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (IntArray::full_shape : Z -> Z -> Assertion)
      (IntArray::seg_shape : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P057_1067B_multihedgehog.rocq.spec_lib */

void *malloc(unsigned long size)
    /*@ malloc_int
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::undef_full(__return, cap)
*/
    /*@ malloc_shape
    With (cap : Z)
    Require 0 <= cap && size == cap * sizeof(int)
    Ensure __return != 0 && IntArray::full_shape(__return, cap)
*/
    ;

void *calloc(unsigned long nmemb, unsigned long size)
    /*@ calloc_int
    With (cap : Z)
    Require 0 <= cap && nmemb == cap && size == sizeof(int)
    Ensure __return != 0 &&
      IntArray::full(__return, cap, repeat_Z(0, cap))
*/
    ;

void free(void *ptr)
    /*@ free_int
    With (cap : Z)
    Require
      0 <= cap && exists values,
        Zlength(values) == cap && IntArray::full(ptr, cap, values)
    Ensure emp
*/
    ;

static int bfs(int src, int *parent, int *dist)

{
    int *q = malloc(n * sizeof(*q))
        ;
    int l = 0, r = 0;
    q[r] = src;
    ++r;

    for (int i = 0; i < n; ++i)
    {
        dist[i] = -1;
        parent[i] = -1;
    }

    dist[src] = 0;
    int far = src;

    while (l < r)
    {
        int v = q[l];
        ++l;
        if (dist[v] > dist[far])
            far = v;

        for (int e = head[v]; e != -1; e = nxt[e])
        {
            if (dist[to[e]] < 0)
            {
                dist[to[e]] = dist[v] + 1;
                parent[to[e]] = v;
                q[r] = to[e];
                ++r;
            }
        }
    }

    free(q) ;
    return far;
}

static int solver(int nn, long long k, const int *eu, const int *ev)

/*@ With (nv : Z) (edges : list (Z * Z))
             (eu_data ev_data : list Z)
             (n_before head_before to_before next_before deg_before : Z)
    Require
      1 <= nv && nv <= 100000 &&
      1 <= k && k <= 1000000000 &&
      Zlength(edges) == nv - 1 &&
      (forall i, (0 <= i && i < Zlength(edges)) =>
        (1 <= fst(edges[i]) && fst(edges[i]) <= nv &&
         1 <= snd(edges[i]) && snd(edges[i]) <= nv)) &&
      Pre(nv, k, edges) &&
      nn == nv && Zlength(eu_data) == Zlength(edges) &&
      Zlength(ev_data) == Zlength(edges) &&
      (forall i, (0 <= i && i < Zlength(edges)) =>
        (eu_data[i] == fst(edges[i]) - 1 &&
         ev_data[i] == snd(edges[i]) - 1)) &&
      IntArray::full(eu, Zlength(edges), eu_data) *
      IntArray::full(ev, Zlength(edges), ev_data) *
      store(&n, int, n_before) *
      store(&head, int *, head_before) * store(&to, int *, to_before) *
      store(&nxt, int *, next_before) * store(&deg, int *, deg_before)
    Ensure
      exists head_after to_after next_after deg_after,
        Spec(nv, k, edges, __return) &&
        IntArray::full(eu, Zlength(edges), eu_data) *
        IntArray::full(ev, Zlength(edges), ev_data) *
        store(&n, int, nv) *
        store(&head, int *, head_after) * store(&to, int *, to_after) *
        store(&nxt, int *, next_after) * store(&deg, int *, deg_after)
*/

{
    n = nn;
    head = malloc(n * sizeof(*head))
        ;
    deg = calloc(n, sizeof(*deg))
        ;
    to = malloc((2 * n - 2) * sizeof(*to))
        ;
    nxt = malloc((2 * n - 2) * sizeof(*nxt))
        ;

    for (int i = 0; i < n; ++i)
        head[i] = -1;

    int ec = 0;
    
    for (int i = 0; i + 1 < n; ++i)
    {
        int u = eu[i], v = ev[i];
        to[ec] = v;
        nxt[ec] = head[u];
        head[u] = ec;
        ++ec;
        to[ec] = u;
        nxt[ec] = head[v];
        head[v] = ec;
        ++ec;
        ++deg[u];
        ++deg[v];
    }

    int *p = malloc(n * sizeof(*p))
        ;
    int *d = malloc(n * sizeof(*d))
        ;
    int ok = 1;

    int a = bfs(0, p, d)
        ;

    int b = bfs(a, p, d)
        ;

    if (d[b] != 2 * k)
        ok = 0;

    int center = b;
    
    for (long long i = 0; ok && i < k; ++i)
        center = p[center];

    if (ok)
    {
        
        bfs(center, p, d)
            ;
    }

    for (int v = 0; ok && v < n; ++v)
    {
        if (d[v] > k || (d[v] == k && deg[v] != 1) ||
            (d[v] < k && ((v == center && deg[v] < 3) || (v != center && deg[v] < 4))))
            ok = 0;
    }

    free(head) ;
    free(to) ;
    free(nxt) ;
    free(deg) ;
    free(p) ;
    free(d) ;
    return ok;
}

// int main(void)
// {
//     long long k;
//     if (scanf("%d %lld", &n, &k) != 2)
//         return 0;
//     int *eu = malloc((size_t)(n - 1) * sizeof(int)), *ev = malloc((size_t)(n - 1) * sizeof(int));
//     for (int i = 0; i < n - 1; ++i)
//     {
//         scanf("%d%d", &eu[i], &ev[i]);
//         --eu[i];
//         --ev[i];
//     }
//     puts(solver(n, k, eu, ev) ? "Yes" : "No");
//     free(eu);
//     free(ev);
//     return 0;
// }
