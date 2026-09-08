#include "priority_queue_decrease_key_def.h"

void pqdk_sift_up(int *key, int *data, int *pos, int data_bound,
                  int n, int idx)
/*@ With (M : partial_map) (capacity : Z)
    Require
      0 <= idx && idx < n &&
      n <= capacity && capacity <= heap_capacity &&
      store_sift_up(
        key, data, pos, data_bound, capacity, M, n, idx
      )
    Ensure
      store_heap(
        key, data, pos, data_bound, capacity, M, n
      )
 */
{
  int child = idx;

  while (child > 0) {
    int parent = (child - 1) / 2;

    if (key[parent] <= key[child]) {
      break;
    }

    int tmp_key = key[parent];
    int tmp_data = data[parent];

    pos[data[parent]] = child;
    pos[data[child]] = parent;
    key[parent] = key[child];
    data[parent] = data[child];
    key[child] = tmp_key;
    data[child] = tmp_data;

    child = parent;
  }
}

void pqdk_sift_down(int *key, int *data, int *pos, int data_bound,
                    int n, int idx)
/*@ With (M : partial_map) (capacity : Z)
    Require
      0 <= idx && idx < n &&
      n <= capacity && capacity <= heap_capacity &&
      store_sift_down(
        key, data, pos, data_bound, capacity, M, n, idx
      )
    Ensure
      store_heap(
        key, data, pos, data_bound, capacity, M, n
      )
 */
{
  int current = idx;

  while (current * 2 + 1 < n) {
    int left = current * 2 + 1;
    int right = left + 1;
    int smallest = left;

    if (right < n && key[right] < key[left]) {
      smallest = right;
    }

    if (key[current] <= key[smallest]) {
      break;
    }

    int tmp_key = key[current];
    int tmp_data = data[current];

    pos[data[current]] = smallest;
    pos[data[smallest]] = current;
    key[current] = key[smallest];
    data[current] = data[smallest];
    key[smallest] = tmp_key;
    data[smallest] = tmp_data;

    current = smallest;
  }
}

void pqdk_push(int *key, int *data, int *pos, int *size,
               int data_bound, int data_x, int key_x)
/*@ With (M_before : partial_map) (n capacity : Z)
    Require
      0 <= n && n < capacity && capacity <= heap_capacity &&
      0 <= data_x && data_x < data_bound &&
      partial_map_absent(M_before, data_x) &&
      store(size, int, n) *
      store_heap(
        key, data, pos, data_bound, capacity, M_before, n
      )
    Ensure
      store(size, int, n + 1) *
      store_heap(
        key, data, pos, data_bound, capacity,
        partial_map_add(M_before, data_x, key_x), n + 1
      )
 */
{
  int n0 = *size;

  key[n0] = key_x;
  data[n0] = data_x;
  pos[data_x] = n0;
  *size = n0 + 1;

  
  pqdk_sift_up(key, data, pos, data_bound, n0 + 1, n0);
}

void pqdk_decrease_key(int *key, int *data, int *pos, int *size,
                       int data_bound, int data_x, int key_x)
/*@ With (M_before : partial_map) (n capacity : Z)
    Require
      0 <= n && n <= capacity && capacity <= heap_capacity &&
      0 <= data_x && data_x < data_bound &&
      partial_map_decrease_key_pre(
        M_before, data_x, key_x
      ) &&
      store(size, int, n) *
      store_heap(
        key, data, pos, data_bound, capacity, M_before, n
      )
    Ensure
      store(size, int, n) *
      store_heap(
        key, data, pos, data_bound, capacity,
        partial_map_update(M_before, data_x, key_x), n
      )
 */
{

  int n0 = *size;
  int idx = pos[data_x];

  key[idx] = key_x;

  
  pqdk_sift_up(key, data, pos, data_bound, n0, idx);
}

void pqdk_update_or_push(int *key, int *data, int *pos, int *size,
                         int data_bound, int data_x, int key_x)
/*@ With (M_before : partial_map) (n capacity : Z)
    Require
      0 <= n && n < capacity && capacity <= heap_capacity &&
      0 <= data_x && data_x < data_bound &&
      partial_map_update_or_add_pre(
        M_before, data_x, key_x
      ) &&
      store(size, int, n) *
      store_heap(
        key, data, pos, data_bound, capacity, M_before, n
      )
    Ensure exists n_after,
      partial_map_update_or_add_size(
        M_before, n, n_after, data_x, key_x
      ) &&
      store(size, int, n_after) *
      store_heap(
        key, data, pos, data_bound, capacity,
        partial_map_update_or_add(M_before, data_x, key_x), n_after
      )
 */
{

  int idx = pos[data_x];
  if (idx < 0) {

    pqdk_push(key, data, pos, size, data_bound, data_x, key_x);
  } else {

    pqdk_decrease_key(key, data, pos, size, data_bound, data_x, key_x);
  }

}

void pqdk_pop(int *key, int *data, int *pos, int *size,
              int data_bound, int *data_out, int *key_out)
/*@ With (M_before : partial_map) (n capacity : Z)
    Require
      1 <= n && n <= capacity && capacity <= heap_capacity &&
      store(size, int, n) *
      store_heap(
        key, data, pos, data_bound, capacity, M_before, n
      ) *
      has_int_permission(data_out) *
      has_int_permission(key_out)
    Ensure exists popped,
      *key_out == item_key(popped) &&
      *data_out == item_data(popped) &&
      partial_map_minimum(M_before, popped) &&
      store(size, int, n - 1) *
      store_heap(
        key, data, pos, data_bound, capacity,
        partial_map_remove(M_before, item_data(popped)), n - 1
      )
 */
{

  int n0 = *size;
  int result_key = key[0];
  int result_data = data[0];
  *key_out = result_key;
  *data_out = result_data;

  pos[result_data] = -1;

  if (n0 == 1) {
    *size = 0;

    return;
  }

  pos[data[n0 - 1]] = 0;
  key[0] = key[n0 - 1];
  data[0] = data[n0 - 1];

  *size = n0 - 1;

  
  pqdk_sift_down(key, data, pos, data_bound, n0 - 1, 0);
}

