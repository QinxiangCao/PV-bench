#include "../pointf.h"
#include "pointf_model.h"

/*@ Import Coq Require Import PVbench.Algorithms.convex_hull_float.rocq.spec_lib */

/*@ Extern Coq
      (pointsf_finite : list PointF -> Prop)
      (all_pointf_cross_finite : list PointF -> Prop)
      (pointf_permutation : list PointF -> list PointF -> Prop)
      (pointf_xy_sorted : list PointF -> Prop)
      (is_andrew_hull_float : list PointF -> list PointF -> list PointF -> Prop)
 */

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
      pointsf_finite(input) && all_pointf_cross_finite(input) &&
      Zlength(hull_init) == 2 * n && pointsf_finite(hull_init) &&
      PointFArray::full(pts, n, input) *
      PointFArray::full(hull, 2 * n, hull_init)
    Ensure
      exists sorted hull_all out,
        pts == pts@pre && hull == hull@pre && n == n@pre &&
        Zlength(sorted) == n && Zlength(hull_all) == 2 * n &&
        out == sublist(0, __return, hull_all) && Zlength(out) == __return &&
        2 <= __return && __return <= 2 * n &&
        pointsf_finite(sorted) && all_pointf_cross_finite(sorted) &&
        pointsf_finite(hull_all) && pointf_permutation(input, sorted) &&
        pointf_xy_sorted(sorted) &&
        is_andrew_hull_float(input, sorted, out) &&
        PointFArray::full(pts, n, sorted) *
        PointFArray::full(hull, 2 * n, hull_all)
 */
{
  quicksort_xy_points(pts, n, 0, n - 1);

  return andrew_build_from_sorted(pts, n, hull);
}
