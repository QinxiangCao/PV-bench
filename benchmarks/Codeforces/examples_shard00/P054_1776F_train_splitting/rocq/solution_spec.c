/* Codeforces 1776/F - Train Splitting */
// #include <stdio.h>
// #include <stdlib.h>

typedef unsigned long size_t;

/*@ Extern Coq
      (pair : {A} {B} -> A -> B -> A * B)
      (Pre : Z -> list (Z * Z) -> Prop)
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : Z -> list (Z * Z) -> Z * list Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import PVbench.Codeforces.examples_shard00.P054_1776F_train_splitting.rocq.spec_lib */

void *calloc(unsigned long nmemb, unsigned long size)
/*@ calloc_int
    With (cap : Z)
    Require
      0 <= cap &&
      nmemb == cap &&
      size == sizeof(int)
    Ensure
      __return != 0 &&
      IntArray::full(__return, cap, repeat_Z(0, cap))
*/;

void free(void *ptr)
/*@ free_int
    Require exists values cap,
      IntArray::full(ptr, cap, values)
    Ensure emp
*/;

static int solver(int n, int m, const int *u, const int *v, int *colors)

/*@ With (e : list (Z * Z))
             (u_data v_data : list Z)
    Require
      3 <= n && n <= 50 &&
      n - 1 <= Zlength(e) && Zlength(e) <= 1225 &&
      (forall i, (0 <= i && i < Zlength(e)) =>
        ((0 <= fst(e[i]) && fst(e[i]) < n) &&
         (0 <= snd(e[i]) && snd(e[i]) < n))) &&
      Pre(n, e) &&
      m == Zlength(e) && Zlength(u_data) == m && Zlength(v_data) == m &&
      (forall i, (0 <= i && i < m) =>
        (u_data[i] == fst(e[i]) && v_data[i] == snd(e[i]))) &&
      IntArray::full(u, m, u_data) * IntArray::full(v, m, v_data) *
      IntArray::undef_full(colors, m)
    Ensure
      exists color_count result,
        Spec(n, e, pair(color_count, result)) && __return == color_count &&
        IntArray::full(u, m, u_data) * IntArray::full(v, m, v_data) *
        IntArray::full(colors, m, result)
*/

{
    int *deg = calloc((size_t)n, sizeof(*deg))
      ;

    for (int i = 0; i < m; ++i) {
        ++deg[u[i]];
        ++deg[v[i]];
    }

    int pivot = -1;
    
    for (int i = 0; i < n; ++i) {
        if (deg[i] < n - 1) {
            pivot = i;
            break;
        }
    }

    int kinds;
    if (pivot >= 0) {
        kinds = 2;
        
        for (int i = 0; i < m; ++i) {
            colors[i] = (u[i] == pivot || v[i] == pivot) ? 1 : 2;
        }
    } else {
        kinds = 3;
        int first = 1;
        
        for (int i = 0; i < m; ++i) {
            if (u[i] == 0 || v[i] == 0) {
                colors[i] = first ? 1 : 2;
                first = 0;
            } else {
                colors[i] = 3;
            }
        }
    }

    free(deg) ;
    return kinds;
}

// int main(void)
// {
//     int t;scanf("%d",&t);while(t--){int n,m;scanf("%d %d",&n,&m);int *u=malloc((size_t)m*sizeof(*u)),*v=malloc((size_t)m*sizeof(*v)),*colors=malloc((size_t)m*sizeof(*colors));
//         for(int i=0;i<m;++i){scanf("%d %d",&u[i],&v[i]);--u[i];--v[i];}
//         printf("%d\n",solver(n,m,u,v,colors));for(int i=0;i<m;++i)printf("%d%c",colors[i],i+1==m?'\n':' ');
//         free(colors);free(u);free(v);
//     }return 0;
// }
