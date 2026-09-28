/*@ Extern Coq
      (strict_increasing : list Z -> Prop)
 */

/*@ Extern Coq
      (discretize_result : list Z -> list Z -> Z -> Prop)
 */

/*@ Import Coq Require Import PVbench.Algorithms.discretize.rocq.spec_lib */

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
    return i + 1;
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
}

void int_array_quicksort(int *arr, int n)

{
    quicksort_range(arr, n, 0, n - 1);
}

int discretize(const int *src, int n, int *dest_map)
/*@ With src_l
    Require 1 <= n && n <= 50000 &&
            IntArray::full(src, n, src_l) *
            IntArray::undef_full(dest_map, n)
    Ensure exists out_l,
            discretize_result(src_l, out_l, __return) &&
            IntArray::full(src, n, src_l) *
            IntArray::full(dest_map, n, out_l)
*/
{

    for (int i = 0; i < n; i++) {
        dest_map[i] = src[i];
    }

    int_array_quicksort(dest_map, n);
    int slow = 0;

    for (int fast = 1; fast < n; fast++) {
        if (dest_map[fast] != dest_map[slow]) {
            slow++;
            dest_map[slow] = dest_map[fast];
        }
    }
    return slow + 1;
}

int query_forward(const int *map, int map_size, int target)
{
    int low = 0;
    int high = map_size - 1;

    while (low <= high) {
        int mid = low + (high - low) / 2;

        if (map[mid] == target) {
            return mid;
        } else if (map[mid] < target) {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    return -1;
}
