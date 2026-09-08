/*@ Import Lean
import Data_structures.priority_queue_index.lean.spec_lib
open scoped SimpleC
*/

/*@ Extern Coq (multiset :: * => *) */
/*@ Extern Coq
      (heap_capacity : Z)
      (heap_item : Z -> Z -> Z * Z)
      (item_key : Z * Z -> Z)
      (item_data : Z * Z -> Z)
      (pair_list : list Z -> list Z -> list (Z * Z))
      (list_to_multiset : {A} -> list A -> multiset A)
      (multiset_size : {A} -> multiset A -> Z)
      (multiset_equiv : {A} -> multiset A -> multiset A -> Prop)
      (multiset_insert :
        {A} -> multiset A -> A -> multiset A)
      (multiset_remove :
        {A} -> multiset A -> A -> multiset A)
      (multiset_min : multiset (Z * Z) -> Z * Z)
      (multiset_minimum :
        multiset (Z * Z) -> Z * Z -> Prop)
      (store_heap :
        Z -> Z -> multiset (Z * Z) -> Z -> Assertion)
      (heap_representation :
        multiset (Z * Z) -> list Z -> list Z -> Z -> Prop)
      (heap_parent : Z -> Z)
      (KeyWriteState :
        multiset (Z * Z) -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (PushSource :
        list Z -> list Z -> multiset (Z * Z) -> Z -> Z -> Z -> Prop)
      (PushLoopState :
        list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (PushResult :
        multiset (Z * Z) -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (BuildPrefixState :
        multiset (Z * Z) -> list Z -> list Z -> Z -> Prop)
      (PrefixMinimum :
        list Z -> list Z -> Z -> Z * Z -> Prop)
      (PopLoopState :
        list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (PopSelectedChild : list Z -> Z -> Z -> Z -> Prop)
      (PopReadyState :
        list Z -> list Z -> list Z -> list Z -> Z -> Z * Z -> Prop)
      (PopResult :
        multiset (Z * Z) ->
        list Z -> list Z -> list Z -> list Z -> Z -> Z * Z -> Prop)
 */


void push(int *key, int *data, int n, int data_x, int key_x)
/*@ With (S_before : multiset (Z * Z))
    Require
      0 <= n &&
      n < heap_capacity &&
      store_heap(key, data, S_before, n)
    Ensure
      store_heap(
        key, data,
        multiset_insert(S_before, heap_item(key_x, data_x)),
        n + 1
      )
 */
{

  key[n] = key_x;

  data[n] = data_x;

  int child = n;

  while (child > 0) {
    int parent = (child - 1) / 2;

    if (key[parent] <= key[child]) {

      break;
    }
    int tmp_key = key[parent];
    key[parent] = key[child];
    key[child] = tmp_key;

    int tmp_data = data[parent];
    data[parent] = data[child];
    data[child] = tmp_data;

    child = parent;
  }

  
}

void build(int *key, int *data, int n)
/*@ With (key_input data_input : list Z)
    Require
      0 <= n &&
      n <= heap_capacity &&
      Zlength(key_input) == n &&
      Zlength(data_input) == n &&
      IntArray::full(key, n, key_input) *
      IntArray::undef_seg(key, n, heap_capacity) *
      IntArray::full(data, n, data_input) *
      IntArray::undef_seg(data, n, heap_capacity)
    Ensure
      store_heap(
        key, data,
        list_to_multiset(pair_list(key_input, data_input)),
        n
      )
 */
{

  for (int i = 1; i < n; ++i) {
    int data_x = data[i];
    int key_x = key[i];

    int child = i;

    while (child > 0) {
      int parent = (child - 1) / 2;

      if (key[parent] <= key[child]) {

        break;
      }
      int tmp_key = key[parent];
      key[parent] = key[child];
      key[child] = tmp_key;

      int tmp_data = data[parent];
      data[parent] = data[child];
      data[child] = tmp_data;

      child = parent;
    }

    
  }

}

void pop(int *key, int *data, int n, int *data_out, int *key_out)
/*@ With (S_before : multiset (Z * Z))
    Require
      1 <= n &&
      store_heap(key, data, S_before, n) *
      has_int_permission(data_out) *
      has_int_permission(key_out)
    Ensure exists popped,
      *key_out == item_key(popped) &&
      *data_out == item_data(popped) &&
      multiset_minimum(S_before, popped) &&
      store_heap(
        key, data,
        multiset_remove(S_before, popped),
        n - 1
      )
 */
{

  int result_key = key[0];
  int result_data = data[0];

  if (n == 1) {

      *key_out = result_key;
      *data_out = result_data;
    return;
  }

  key[0] = key[n - 1];
  data[0] = data[n - 1];

  int idx = 0;

  while (idx * 2 + 1 < n - 1) {
    int left = idx * 2 + 1;
    int right = left + 1;
    int smallest = left;

    if (right < n - 1 && key[right] < key[left]) {
      smallest = right;
    }

    if (key[idx] <= key[smallest]) {

      break;
    }
    int tmp_key = key[idx];
    key[idx] = key[smallest];
    key[smallest] = tmp_key;

    int tmp_data = data[idx];
    data[idx] = data[smallest];
    data[smallest] = tmp_data;

    idx = smallest;
  }

  

  *key_out = result_key;
  *data_out = result_data;
  return;
}

