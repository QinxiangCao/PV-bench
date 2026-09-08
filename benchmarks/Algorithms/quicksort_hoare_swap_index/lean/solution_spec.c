/*@ Import Lean
import AUXLib.Sorting
import SimpleC.SL.SeparationLogic
open AUXLib
open scoped SimpleC
*/
void swap(int *arr, int i, int j)

{
  int tmp = arr[i];
  arr[i] = arr[j];
  arr[j] = tmp;
}

int partition(int *arr, int low, int high)

{
  int pivot = arr[low];
  int i = low;
  int j = high;

  while (i < j) {

    while (i < j && arr[j] >= pivot) {
      j--;
    }

    while (i < j && arr[i] <= pivot) {
      i++;
    }
    if (i < j) {
      swap(arr, i, j) ;
    }
  }

  swap(arr, low, i) ;
  return i ;
}

void quicksort_range(int *arr, int left, int right)

{
  int p = partition(arr, left, right) ;
  if (p > left) {
    quicksort_range(arr, left, p - 1) ;
  }
  if (p < right) {
    quicksort_range(arr, p + 1, right) ;
  }
  return ;
}

void quicksort(int *arr, int n)
/*@ With (l : list Z)
    Require 0 <= n && n <= 50000 &&
            IntArray::full(arr, n, l)
    Ensure exists l1,
            Permutation(l, l1) &&
            Sorting::increasing(l1) &&
            IntArray::full(arr, n, l1)
*/
{
  if (n > 0) {
    quicksort_range(arr, 0, n - 1) ;
  }
  return ;
}
