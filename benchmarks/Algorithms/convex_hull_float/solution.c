#include "pointf.h"

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

{
  quicksort_xy_points(pts, n, 0, n - 1);

  return andrew_build_from_sorted(pts, n, hull);
}
