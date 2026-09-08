/*@ Import Coq Require Import PVbench.Algorithms.kosaraju.rocq.spec_lib */
/*@ Extern Coq (AdjGraph :: *) */
/*@ Extern Coq
               (mutually_reachable: AdjGraph -> Z -> Z -> Prop)
               (AdjGraphValid: AdjGraph -> Prop)
               (csr_wf2_core: AdjGraph -> list Z -> list Z -> Prop)
               (csr2_faithful: AdjGraph -> list Z -> list Z -> Prop)
               (adj_verts: AdjGraph -> Z)
               (m_of: list Z -> Z)
               (csr_lo: Z -> list Z -> Z)
               (Znth: {A} -> Z -> list A -> A -> A)
                */
void dfs1(int const u, int const n,
          int const *const radj_col, int const *const radj_row,
          int *const vis1, int *const fin, int *const timer_p);
void dfs2(int const root, int const u, int const n,
          int const *const fadj_col, int const *const fadj_row,
          int *const vis2, int *const sid);

/* Working-array allocator / deallocator */
int *malloc_int_array(int n);

void free_int_array(int *a);

/* DFS phases are internal helper routines of the complete algorithm. */

/* ==================================================================== */
/* transpose: counting-sort CSR transpose of the forward graph.        */
/*   Inputs : fadj_col[fadj_row[u] .. fadj_row[u+1]-1] = out-neighbours*/
/*            of u, i.e. forward edges (u -> v) packed in CSR.         */
/*   Outputs: radj_col/radj_row = reverse CSR, where radj_col          */
/*            [radj_row[v] .. radj_row[v+1]-1] = in-neighbours of v    */
/*            = { u | edge u->v }.                                      */
/*   pos   : scratch cursor array of length n (malloc'd by caller),    */
/*           used as the moving write head during the scatter pass so  */
/*           radj_row stays in prefix-sum (offset) form.               */
/*   Algorithm (standard CSR transpose):                                */
/*     pass 1: count in-degree of each v into radj_row[0..n-1]          */
/*     pass 2: prefix-sum radj_row (radj_row[v]=bucket start of v);    */
/*             radj_row[n] = m.  Copy radj_row -> pos (write heads).    */
/*     pass 3: for each vertex u, scan its forward neighbour range; for */
/*             each edge (u,v) write u at radj_col[pos[v]], pos[v]++.   */
/*             The outer loop carries u, so no CSR inverse lookup.     */
/*   Postcondition: transpose_spec (csr1_faithful + csr_wf1).          */
/*   high_level_spec <= low_level_spec (no monad; pure arrays).         */
/* ==================================================================== */

void transpose(int n, int m,
               int *fadj_col, int *fadj_row,
               int *radj_col, int *radj_row, int *pos)

{
  /* pass 1: zero the in-degree counters in radj_row[0..n-1] */

  for (int v = 0; v < n; v++) {

    radj_row[v] = 0;
  }
  /* pass 2: count in-degrees: for each forward edge (u, v=fadj_col[j]),
     increment radj_row[v] */

  for (int j = 0; j < m; j++) {

    int v = fadj_col[j];

    radj_row[v] = radj_row[v] + 1;
  }
  /* pass 3: prefix-sum: radj_row[v] = offset of v's in-bucket;
     radj_row[n] = total edge count = m.  Copy offsets into pos. */
  int sum = 0;

  for (int v = 0; v < n; v++) {

    int deg = radj_row[v];
    radj_row[v] = sum;
    pos[v] = sum;
    sum = sum + deg;
  }
  radj_row[n] = sum;
  /* pass 4: scatter.  Outer loop over source vertex u; inner loop over
     u's forward neighbour range [fadj_row[u], fadj_row[u+1]).  For each
     edge (u,v): radj_col[pos[v]] := u; pos[v]++.  radj_row is untouched
     and stays in offset form. */

  for (int u = 0; u < n; u++) {

    int lo = fadj_row[u];
    int hi = fadj_row[u + 1];
    int j = lo;

    while (j < hi) {
      int v = fadj_col[j];

      int p = pos[v];

      radj_col[p] = u;
      pos[v] = p + 1;
      j = j + 1;
    }
  }

}

/* ==================================================================== */
/* kosaraju: top-level SCC driver (direct-proof external interface,    */
/*   mirroring kmp_rel.c:main).  Takes the forward CSR + an output sid */
/*   buffer; mallocs all working arrays internally and frees them      */
/*   before return, so the external spec mentions only fadj_* and sid. */
/*   Composes: transpose -> phase-1 dfs1 sweep -> sort_by_fin ->       */
/*   phase-2 dfs2 sweep over the sorted order.                         */
/*   Ensure: the output sid labels vertices so that                    */
/*     sid[u] = sid[v]  <=>  mutually_reachable g u v   (same SCC).    */
/* ==================================================================== */
void kosaraju(int n, int *fadj_col, int *fadj_row, int *sid)
/*@ With g fadj_col_l fadj_row_l sid_l
    Require
      1 <= n && n <= 2147483646 &&
      csr2_faithful(g, fadj_col_l, fadj_row_l) &&
      AdjGraphValid(g) &&
      csr_wf2_core(g, fadj_col_l, fadj_row_l) &&
      csr_lo(0, fadj_row_l) == 0 &&
      adj_verts(g) == n &&
      m_of(fadj_row_l) > 0 &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(sid, n, sid_l)
    Ensure
      exists sid_l_,
      (forall (u: Z), (0 <= u && u < n) =>
         (forall (v: Z), (0 <= v && v < n) =>
            ((Znth(u, sid_l_, 0) == Znth(v, sid_l_, 0) => mutually_reachable(g, u, v))
             && (mutually_reachable(g, u, v) => Znth(u, sid_l_, 0) == Znth(v, sid_l_, 0))))) &&
      IntArray::full(fadj_col, m_of(fadj_row_l), fadj_col_l) *
      IntArray::full(fadj_row, n + 1, fadj_row_l) *
      IntArray::full(sid, n, sid_l_)
*/
{
  int m = fadj_row[n];
  int *radj_col = malloc_int_array(m);
  int *radj_row = malloc_int_array(n + 1);
  int *pos = malloc_int_array(n);
  int *vis1 = malloc_int_array(n);
  int *fin = malloc_int_array(n);
  int *vis2 = malloc_int_array(n);
  int timer = 0;

  /* capture the arbitrary contents returned by malloc for the working
     arrays that transpose will overwrite. */

  /* initialise vis1 and vis2 to zero */

  for (int u = 0; u < n; u++) {

    vis1[u] = 0;
    vis2[u] = 0;
  }
  /* capture the zeroed working arrays (vis1_zero/vis2_zero). */

  /* step C: build the reverse CSR from the forward CSR.  The working
     arrays' pre-call contents (radj_col_l0/radj_row_l0/pos_l0) are
     arbitrary; transpose overwrites them. */

  /* step A (phase 1): for each unvisited1 vertex, run dfs1 on the
     reverse graph to assign finish times.  Loop invariant threads the
     visited1/fin/timer arrays; each dfs1 call refines them. */

  for (int u = 0; u < n; u++) {

    if (vis1[u] == 0) {

      dfs1(u, n, radj_col, radj_row, vis1, fin, &timer)
          ;

    }
  }

  /* Reuse pos, which transpose no longer needs, as the decreasing
     finish-time traversal order required by phase 2. */

  for (int i = 0; i < n; i++) {
    pos[i] = fin[n - 1 - i];
  }

  /* step B (phase 2): sweep the sorted order; for each unvisited2 root,
     run dfs2(root, root, ...) to label its whole SCC. */

  for (int k = 0; k < n; k++) {

    int root = pos[k];

    if (vis2[root] == 0) {
      /* Pre-set sid[root] = root.  dfs2 itself performs the visited2 write;
         keeping root unvisited at the call boundary matches the abstract
         Kosaraju phase-2 theorem for a fresh SCC round. */
      /* pre-mark: sid[root] = root.  dfs2 reads sid[root] and labels
         every vertex in root's SCC with sid[root]; setting sid[root]=root
         BEFORE the call makes the SCC representative equal to root itself
         (standard Kosaraju structure).  Same write-before pattern. */
      sid[root] = root;
      /* dfs2 pre-call Assert: expose the POST-write sid state while keeping
         vis2[root] == 0.  phase2_spec is the top-level phase-2 entry for
         dfs2(root, root, ...). */

      dfs2(root, root, n, fadj_col, fadj_row, vis2, sid)
          ;
      /* post-call Assert: capture phase2_spec's high-level and SCC facts. */

    }
  }

  /* post-phase-2: re-expose all working arrays with their lengths in the
     form free_int_array expects (radj_col length = m, others length n). */

  /* free all working arrays.  The final sid array carries the SCC
     labeling (sid_m final); the external Ensure's sid_l_ is sid_m. */
  free_int_array(radj_col) ;
  free_int_array(radj_row) ;
  free_int_array(pos)      ;
  free_int_array(vis1)     ;
  free_int_array(fin)      ;
  free_int_array(vis2)     ;
}
