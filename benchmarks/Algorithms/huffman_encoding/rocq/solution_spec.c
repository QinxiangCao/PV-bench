/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (HuffmanOptimalCost : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.huffman_encoding.rocq.spec_lib */

int huffman_cost(int *weights, int n)
/*@ With (weights_l : list Z)
    Require
      1 <= n && n <= 8 &&
      Zlength(weights_l) == n &&
      Forall(Z::le(1), weights_l) && Forall(Z::ge(1000), weights_l) &&
      IntArray::full(weights, n, weights_l)
    Ensure
      HuffmanOptimalCost(weights_l, __return) &&
      IntArray::full(weights, n, weights_l)
 */
{
  int work[8];

  for (int i = 0; i < n; ++i) {
    work[i] = weights[i];
  }

  int active = n;
  int total = 0;

  while (active > 1) {
    int first = 0;

    for (int i = 1; i < active; ++i) {

      if (work[i] < work[first]) {
        first = i;
      }
    }

    int x = work[first];
    --active;

    work[first] = work[active];

    int second = 0;

    for (int i = 1; i < active; ++i) {
      if (work[i] < work[second]) {
        second = i;
      }
    }

    int y = work[second];
    --active;

    work[second] = work[active];

    int merged = x + y;
    total += merged;
    work[active] = merged;
    ++active;
  }

  return total;
}
