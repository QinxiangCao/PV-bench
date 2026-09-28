#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (MaximumContainerArea : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.container_with_most_water_linear.rocq.spec_lib */

int maxAreaLinear(const int *height, int heightSize)
/*@ With (l : list Z)
    Require
      2 <= heightSize && heightSize <= 100000 &&
      height != 0 &&
      Zlength(l) == heightSize &&
      IntArray::full(height, heightSize, l) &&
      Forall(Z::le(0), l) && Forall(Z::ge(10000), l)
    Ensure
      MaximumContainerArea(l, __return) &&
      IntArray::full(height, heightSize, l)
 */
{
    int left;
    int right;
    int maximumArea;

    if (height == 0 || heightSize < 2) {
        return 0;
    }

    left = 0;
    right = heightSize - 1;
    maximumArea = 0;

    while (left < right) {
        int width = right - left;
        int shorterHeight;
        int area;

        if (height[left] < height[right]) {
            shorterHeight = height[left];
        } else {
            shorterHeight = height[right];
        }

        area = width * shorterHeight;
        if (area > maximumArea) {
            maximumArea = area;
        }

        if (height[left] < height[right]) {
            ++left;
        } else {
            --right;
        }
    }

    return maximumArea;
}
