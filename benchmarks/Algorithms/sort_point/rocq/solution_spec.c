/*@ Import Coq Require Import PVbench.Algorithms.sort_point.rocq.spec_lib */
/*@ Extern Coq (Z::ge : Z -> Z -> Prop) */
/*@ Extern Coq (map : {A B} -> (A -> B) -> list A -> list B) */
/*@ Extern Coq (Z::le : Z -> Z -> Prop) */
/*@ Extern Coq (Forall : {A} -> (A -> Prop) -> list A -> Prop) */
/*@ Extern Coq (point :: *) */
/*@ Extern Coq (mk_point : Z -> Z -> point) */
/*@ Extern Coq (point_x : point -> Z) */
/*@ Extern Coq (point_y : point -> Z) */
/*@ Extern Coq (default_point : point) */
/*@ Extern Coq (FlatPoints : list Z -> list point -> Prop) */
/*@ Extern Coq (PointPermutation : list point -> list point -> Prop) */
/*@ Extern Coq (PolarCmpResult : point -> point -> point -> Z -> Prop) */
/*@ Extern Coq (PolarLe : point -> point -> point -> Prop) */
/*@ Extern Coq (PolarSorted : point -> list point -> Prop) */
struct Point {
  int x;
  int y;
};

static struct Point gp;

int cmp_polar_values(int gx, int gy, int a_x, int a_y, int b_x, int b_y)

{
  int adx = a_x - gx;
  int ady = a_y - gy;
  int bdx = b_x - gx;
  int bdy = b_y - gy;
  int cr = adx * bdy - ady * bdx;
  int da = adx * adx + ady * ady;
  int db = bdx * bdx + bdy * bdy;

  int ah = 0;
  if (ady > 0) {
    ah = 1;
  } else {
    if (ady == 0) {
      if (adx >= 0) {
        ah = 1;
      }
    }
  }

  int bh = 0;
  if (bdy > 0) {
    bh = 1;
  } else {
    if (bdy == 0) {
      if (bdx >= 0) {
        bh = 1;
      }
    }
  }

  if (ah > bh)
    return -1;
  if (ah < bh)
    return 1;

  if (cr > 0)
    return -1;
  if (cr < 0)
    return 1;

  if (da < db)
    return -1;
  if (da > db)
    return 1;

  if (a_x < b_x)
    return -1;
  if (a_x > b_x)
    return 1;
  if (a_y < b_y)
    return -1;
  if (a_y > b_y)
    return 1;
  return 0;
}

void swap_points(int *coords, int n, int i, int j)

{
  int tmp_x = coords[2 * i];
  int tmp_y = coords[2 * i + 1];
  coords[2 * i] = coords[2 * j];
  coords[2 * i + 1] = coords[2 * j + 1];
  coords[2 * j] = tmp_x;
  coords[2 * j + 1] = tmp_y;
}

int partition_points(int *coords, int n, int low, int high, int gx, int gy)

{
  int pivot_x = coords[2 * high];
  int pivot_y = coords[2 * high + 1];
  int i = low - 1;

  for (int j = low; j < high; j++) {
    int ax = coords[2 * j];
    int ay = coords[2 * j + 1];
    int c = cmp_polar_values(gx, gy, ax, ay, pivot_x, pivot_y);

    if (c <= 0) {
      i++;
      swap_points(coords, n, i, j) ;
    }
  }

  swap_points(coords, n, i + 1, high) ;
  return i + 1;
}

void quicksort_points_range(int *coords, int n, int left, int right, int gx, int gy)

{
  if (left < right) {

    int p = partition_points(coords, n, left, right, gx, gy) ;
    if (p > left) {
      quicksort_points_range(coords, n, left, p - 1, gx, gy);
    }
    if (p < right) {
      quicksort_points_range(coords, n, p + 1, right, gx, gy);
    }
  }
}

void sort(struct Point *pts, int n)
/*@ With (flat : list Z) (pts_l : list point) gx gy
    Require
      0 <= n && n <= 50000 &&
      Zlength(pts_l) == n &&
      FlatPoints(flat, pts_l) &&
      Forall(Z::le(-10000), map(point_x, cons(mk_point(gx, gy), pts_l))) &&
          Forall(Z::ge(10000), map(point_x, cons(mk_point(gx, gy), pts_l))) &&
          Forall(Z::le(-10000), map(point_y, cons(mk_point(gx, gy), pts_l))) &&
          Forall(Z::ge(10000), map(point_y, cons(mk_point(gx, gy), pts_l))) &&
      gp.x == gx && gp.y == gy &&
      IntArray::full(pts, 2 * n, flat)
    Ensure
      exists flat_out pts_out,
        FlatPoints(flat_out, pts_out) &&

        PointPermutation(pts_l, pts_out) &&
        PolarSorted(mk_point(gx, gy), pts_out) &&
        gp.x == gx && gp.y == gy &&
        IntArray::full(pts, 2 * n, flat_out)
 */
{
  int *coords = (int *)pts;
  int gx = gp.x;
  int gy = gp.y;
  quicksort_points_range(coords, n, 0, n - 1, gx, gy);
}
