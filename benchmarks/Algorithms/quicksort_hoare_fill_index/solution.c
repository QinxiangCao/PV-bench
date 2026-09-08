int partition(int *arr, int low, int high)

{
  int pivot = arr[low];
  int i = low;
  int j = high;

  while (1) {

    while (i < j && arr[j] > pivot) {
      j--;
    }
    if (i < j) {
      arr[i] = arr[j];
      i++;
    }
    else {
      break;
    }

    while (i < j && arr[i] <= pivot) {
      i++;
    }
    if (i < j) {
      arr[j] = arr[i];
      j--;
    }
    else {
      break;
    }
  }

  arr[i] = pivot;
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

{
  if (n > 0) {
    quicksort_range(arr, 0, n - 1) ;
  }
  return ;
}
