/*@ Import Coq Require Import PVbench.Algorithms.convex_hull_float.rocq.spec_lib */
/*@ Extern Coq Record PointF {
      pointf_x : fp32;
      pointf_y : fp32;
    } */
/*@ Extern Coq (In : {A} -> A -> list A -> Prop) */
/*@ Extern Coq (Forall : {A} -> (A -> Prop) -> list A -> Prop) */
/*@ Extern Coq (map : {A B} -> (A -> B) -> list A -> list B) */
/*@ Extern Coq (fp32_isFinite : fp32 -> Prop) */
/*@ Extern Coq (fp32_sub : fp32 -> fp32 -> fp32) */
/*@ Extern Coq (fp32_mul : fp32 -> fp32 -> fp32) */
/*@ Extern Coq (pointf_permutation : list PointF -> list PointF -> Prop) */
/*@ Extern Coq (pointf_xy_sorted : list PointF -> Prop) */
/*@ Extern Coq (pointf_xy_sorted_range : list PointF -> Z -> Z -> Prop) */
/*@ Extern Coq (is_andrew_hull_float : list PointF -> list PointF -> list PointF -> Prop) */
/*@ Extern Coq (pointf_get_x : PointF -> fp32) */
/*@ Extern Coq (pointf_get_y : PointF -> fp32) */
/*@ Extern Coq (default_pointf : PointF) */
/*@ Extern Coq (store_pointf : Z -> PointF -> Assertion) */
/*@ Extern Coq (undef_pointf : Z -> Assertion) */
/*@ Extern Coq (pointf_cmp_xy : PointF -> PointF -> Z) */
/*@ Extern Coq (pointf_cross : PointF -> PointF -> PointF -> fp32) */
/*@ Extern Coq (PointFArray::full : Z -> Z -> list PointF -> Assertion) */
/*@ Extern Coq (PointFArray::missing_i : Z -> Z -> Z -> Z -> list PointF -> Assertion) */
/*@ Extern Coq (PointFArray::seg : Z -> Z -> Z -> list PointF -> Assertion) */
/*@ Extern Coq (PointFArray::undef_full : Z -> Z -> Assertion) */
/*@ Extern Coq (PointFArray::undef_seg : Z -> Z -> Z -> Assertion) */
/*@ Extern Coq (Znth : {A} -> Z -> list A -> A -> A) */
struct PointF { float x; float y; };

static int point_cmp_xy(float ax, float ay, float bx, float b_y)

{
  if (ax < bx) return -1;
  if (ax > bx) return 1;
  if (ay < b_y) return -1;
  if (ay > b_y) return 1;
  return 0;
}

static float point_cross(float ax, float ay, float bx, float b_y,
                         float cx, float cy)

{
  return (bx - ax) * (cy - ay) - (b_y - ay) * (cx - ax);
}

static void swap_points(struct PointF *pts, int n, int i, int j)

{
  float tx = pts[i].x;
  float ty = pts[i].y;
  pts[i].x = pts[j].x;
  pts[i].y = pts[j].y;
  pts[j].x = tx;
  pts[j].y = ty;
}

static int partition_xy_points(struct PointF *pts, int n, int low, int high)

{
  float pivot_x = pts[high].x;
  float pivot_y = pts[high].y;
  int i = low - 1;

  for (int j = low; j < high; ++j) {
    float ax = pts[j].x;
    float ay = pts[j].y;
    int c = point_cmp_xy(ax, ay, pivot_x, pivot_y);
    if (c <= 0) {
      ++i;
      if (i != j)
        swap_points(pts, n, i, j);
    }
  }
  ++i;
  if (i != high)
    swap_points(pts, n, i, high);
  return i;
}

static void quicksort_xy_points(struct PointF *pts, int n, int left, int right)

{
  if (left < right) {
    int p = partition_xy_points(pts, n, left, right);
    if (p > left)
      quicksort_xy_points(pts, n, left, p - 1);
    if (p < right)
      quicksort_xy_points(pts, n, p + 1, right);
  }
}

static int andrew_build_from_sorted(
    struct PointF *pts, int n, struct PointF *hull)

{
  int k = 0;

  for (int i = 0; i < n; ++i) {

    while (k >= 2) {
      if (((hull[k - 1].x - hull[k - 2].x) *
           (pts[i].y - hull[k - 2].y) -
           (hull[k - 1].y - hull[k - 2].y) *
           (pts[i].x - hull[k - 2].x)) > 0.0f)
        break;
      --k;
    }
    hull[k].x = pts[i].x;
    hull[k].y = pts[i].y;
    ++k;
  }

  int lower_n = k;

  for (int i = n - 2; i >= 0; --i) {

    while (k > lower_n) {
      if (((hull[k - 1].x - hull[k - 2].x) *
           (pts[i].y - hull[k - 2].y) -
           (hull[k - 1].y - hull[k - 2].y) *
           (pts[i].x - hull[k - 2].x)) > 0.0f)
        break;
      --k;
    }
    hull[k].x = pts[i].x;
    hull[k].y = pts[i].y;
    ++k;
  }
  --k;
  return k;
}

int convex_hull_float(struct PointF *pts, int n, struct PointF *hull)
/*@ With (input hull_init : list PointF)
    Require
      2 <= n && n <= 50000 && Zlength(input) == n &&
      Forall(fp32_isFinite, map(pointf_get_x, input)) &&
          Forall(fp32_isFinite, map(pointf_get_y, input)) && (forall (pa : PointF) (pb : PointF) (pc : PointF),
          (In(pa, input) && In(pb, input) && In(pc, input)) =>
          (fp32_isFinite(fp32_sub(pointf_get_x(pb), pointf_get_x(pa))) &&
          fp32_isFinite(fp32_sub(pointf_get_y(pc), pointf_get_y(pa))) &&
          fp32_isFinite(fp32_sub(pointf_get_y(pb), pointf_get_y(pa))) &&
          fp32_isFinite(fp32_sub(pointf_get_x(pc), pointf_get_x(pa))) &&
          fp32_isFinite(fp32_mul(fp32_sub(pointf_get_x(pb), pointf_get_x(pa)), fp32_sub(pointf_get_y(pc), pointf_get_y(pa)))) &&
          fp32_isFinite(fp32_mul(fp32_sub(pointf_get_y(pb), pointf_get_y(pa)), fp32_sub(pointf_get_x(pc), pointf_get_x(pa)))) &&
          fp32_isFinite(pointf_cross(pa, pb, pc)))) &&
      Zlength(hull_init) == 2 * n && Forall(fp32_isFinite, map(pointf_get_x, hull_init)) &&
          Forall(fp32_isFinite, map(pointf_get_y, hull_init)) &&
      PointFArray::full(pts, n, input) *
      PointFArray::full(hull, 2 * n, hull_init)
    Ensure
      exists sorted hull_all out,

        out == sublist(0, __return, hull_all) && Zlength(out) == __return &&
        is_andrew_hull_float(input, sorted, out) &&
        PointFArray::full(pts, n, sorted) *
        PointFArray::full(hull, 2 * n, hull_all)
 */
{
  quicksort_xy_points(pts, n, 0, n - 1);

  return andrew_build_from_sorted(pts, n, hull);
}
