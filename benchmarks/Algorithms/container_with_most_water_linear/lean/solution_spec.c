/*@ Import Lean
import Algorithms.container_with_most_water_linear.lean.spec_lib
open scoped SimpleC
*/

/*@ Extern Coq
      (MaximumContainerArea : list Z -> Z -> Prop)
 */

/*
 * Linear-time two-pointer implementation of Container With Most Water.
 * The input array is only read and is never modified.
 */
int maxAreaLinear(const int *height, int heightSize)
/*@ With (l : list Z)
    Require
      2 <= heightSize && heightSize <= 100000 &&
      height != 0 &&
      Zlength(l) == heightSize &&
      IntArray::full(height, heightSize, l) &&
      (forall (k : Z),
        (0 <= k && k < heightSize) =>
        (0 <= l[k] && l[k] <= 10000))
    Ensure
      MaximumContainerArea(l, __return) &&
      0 <= __return && __return <= 999990000 &&
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

        /*
         * Moving the taller side cannot improve the current shorter side:
         * the width becomes smaller while the usable height cannot exceed
         * the shorter endpoint.  Therefore discard the shorter endpoint.
         */
        if (height[left] < height[right]) {
            ++left;
        } else {
            --right;
        }
    }

    return maximumArea;
}
