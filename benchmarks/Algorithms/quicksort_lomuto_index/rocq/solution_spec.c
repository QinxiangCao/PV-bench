void swap(int *arr, int i, int j)

{
  int tmp = arr[i];
  arr[i] = arr[j];
  arr[j] = tmp;
}

int partition(int *arr, int n, int low, int high)

{
  int pivot = arr[high];
  int i = low - 1;

  for (int j = low; j < high; j++) {
    if (arr[j] <= pivot) {
      i++;
      swap(arr, i, j);
    }
  }

  swap(arr, i + 1, high);
  return i + 1 ;
}

void quicksort_range(int *arr, int n, int left, int right)

{
  if (left < right) {
    int p = partition(arr, n, left, right);
    if (p > left) {
      quicksort_range(arr, n, left, p - 1);
    }
    if (p < right) {
      quicksort_range(arr, n, p + 1, right);
    }
  }
  return ;
}

void quicksort(int *arr, int n)
/*@ With l
    Require 1 <= n && n <= 50000 &&
            IntArray::full(arr, n, l)
    Ensure exists l1,
            Permutation(l, l1) &&
            increasing(l1) &&
            IntArray::full(arr, n, l1)
*/
{
  quicksort_range(arr, n, 0, n - 1);
  return ;
}
