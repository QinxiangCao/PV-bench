/*@ Import Lean
import Algorithms.container_with_most_water_nlogn.lean.spec_lib
open scoped SimpleC
*/

/*@ Extern Coq
      (MaximumContainerArea : list Z -> Z -> Prop)
      (SortedHeightIndexWorkspaceNLogN : list Z -> list Z -> list Z -> Prop)
 */
void mergeHeightIndexRunsNLogN(
    int *sourceHeight, int *sourceIndex,
    int *destinationHeight, int *destinationIndex,
    int count, int left, int middle, int right)

{
    int i = left;
    int j = middle;
    int output = left;

    while (i < middle && j < right) {
        if (sourceHeight[i] >= sourceHeight[j]) {
            destinationHeight[output] = sourceHeight[i];
            destinationIndex[output] = sourceIndex[i];
            i++;
        } else {
            destinationHeight[output] = sourceHeight[j];
            destinationIndex[output] = sourceIndex[j];
            j++;
        }
        output++;
    }

    while (i < middle) {
        destinationHeight[output] = sourceHeight[i];
        destinationIndex[output] = sourceIndex[i];
        i++;
        output++;
    }

    while (j < right) {
        destinationHeight[output] = sourceHeight[j];
        destinationIndex[output] = sourceIndex[j];
        j++;
        output++;
    }
}

void sortHeightIndexRangeNLogN(
    int *workHeight, int *workIndex,
    int *bufferHeight, int *bufferIndex,
    int count, int left, int right)

{
    if (right - left <= 1) {
        return;
    }

    int middle = left + (right - left) / 2;
    sortHeightIndexRangeNLogN(
        workHeight, workIndex, bufferHeight, bufferIndex,
        count, left, middle);
    sortHeightIndexRangeNLogN(
        workHeight, workIndex, bufferHeight, bufferIndex,
        count, middle, right);

    mergeHeightIndexRunsNLogN(
        workHeight, workIndex, bufferHeight, bufferIndex,
        count, left, middle, right);

    for (int k = left; k < right; ++k) {
        workHeight[k] = bufferHeight[k];
        workIndex[k] = bufferIndex[k];
    }
}

int maxAreaNLogN(
    const int *height, int heightSize,
    int *workHeight, int *workIndex,
    int *bufferHeight, int *bufferIndex)
/*@ With (l : list Z)
    Require
      2 <= heightSize && heightSize <= 100000 &&
      Zlength(l) == heightSize &&
      (forall (k : Z),
        (0 <= k && k < heightSize) =>
        (0 <= l[k] && l[k] <= 10000)) &&
      IntArray::full(height, heightSize, l) *
      IntArray::undef_full(workHeight, heightSize) *
      IntArray::undef_full(workIndex, heightSize) *
      IntArray::undef_full(bufferHeight, heightSize) *
      IntArray::undef_full(bufferIndex, heightSize)
    Ensure
      exists sorted_h sorted_i buffer_h buffer_i,
      MaximumContainerArea(l, __return) &&
      0 <= __return && __return <= 999990000 &&
      SortedHeightIndexWorkspaceNLogN(l, sorted_h, sorted_i) &&
      IntArray::full(height, heightSize, l) *
      IntArray::full(workHeight, heightSize, sorted_h) *
      IntArray::full(workIndex, heightSize, sorted_i) *
      IntArray::full(bufferHeight, heightSize, buffer_h) *
      IntArray::full(bufferIndex, heightSize, buffer_i)
 */
{

    for (int k = 0; k < heightSize; ++k) {
        int h = height[k];
        workHeight[k] = h;
        workIndex[k] = k;
        bufferHeight[k] = h;
        bufferIndex[k] = k;
    }

    sortHeightIndexRangeNLogN(
        workHeight, workIndex, bufferHeight, bufferIndex,
        heightSize, 0, heightSize);

    int minimumIndex = workIndex[0];
    int maximumIndex = workIndex[0];
    int maximumArea = 0;

    for (int k = 1; k < heightSize; ++k) {
        int index = workIndex[k];
        int currentHeight = workHeight[k];
        int distanceToMinimum = index - minimumIndex;
        int distanceToMaximum = maximumIndex - index;

        if (distanceToMinimum < 0) {
            distanceToMinimum = -distanceToMinimum;
        }
        if (distanceToMaximum < 0) {
            distanceToMaximum = -distanceToMaximum;
        }

        int width;
        if (distanceToMinimum > distanceToMaximum) {
            width = distanceToMinimum;
        } else {
            width = distanceToMaximum;
        }

        int area = width * currentHeight;
        if (area > maximumArea) {
            maximumArea = area;
        }

        if (index < minimumIndex) {

            minimumIndex = index;
        }
        if (index > maximumIndex) {

            maximumIndex = index;
        }
    }

    return maximumArea;
}
