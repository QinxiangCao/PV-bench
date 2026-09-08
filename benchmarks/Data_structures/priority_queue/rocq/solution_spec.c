/*@ Extern Coq (multiset :: * => *) */
/*@ Extern Coq
      (heap_capacity : Z)
      (mlist : {A} -> multiset A -> list A)
      (list_to_multiset : {A} -> list A -> multiset A)
      (multiset_size : {A} -> multiset A -> Z)
      (multiset_equiv : {A} -> multiset A -> multiset A -> Prop)
      (multiset_insert : {A} -> multiset A -> A -> multiset A)
      (multiset_remove :
        {A} -> multiset A -> A -> multiset A)
      (multiset_max : multiset Z -> Z)
      (multiset_maximum : multiset Z -> Z -> Prop)
      (store_heap : Z -> multiset Z -> Z -> Assertion)
      (heap_retired_cell : Z -> Z -> Z -> Assertion)
      (heap_representation :
        multiset Z -> list Z -> Z -> Prop)
      (PrefixMaximum : list Z -> Z -> Z -> Prop)
      (PushSource : list Z -> multiset Z -> Z -> Z -> Prop)
      (PushLoopState : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (PushResult : multiset Z -> list Z -> Z -> Z -> Prop)
      (BuildPrefixState : multiset Z -> list Z -> Z -> Prop)
      (heap_parent : Z -> Z)
      (PopLoopState : list Z -> list Z -> Z -> Z -> Prop)
      (PopSelectedChild : list Z -> Z -> Z -> Z -> Prop)
      (PopReadyState : list Z -> list Z -> Z -> Z -> Prop)
      (PopResult :
        multiset Z -> list Z -> list Z -> Z -> Z -> Prop)
      (HeapSortState :
        list Z -> multiset Z -> list Z -> Prop)
      (Permutation : list Z -> list Z -> Prop)
      (increasing : list Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Data_structures.priority_queue.rocq.spec_lib */

void push(int *heap, int n, int x)
/*@ With (S_before : multiset Z)
    Require
      n < heap_capacity &&
      store_heap(heap, S_before, n) *
      IntArray::undef_seg(heap, n, n + 1)
    Ensure
      store_heap(
        heap, multiset_insert(S_before, x), n + 1
      )
 */
{

  heap[n] = x;

  int child = n;

  while (child > 0) {
    int parent = (child - 1) / 2;

    if (heap[parent] >= heap[child]) {

      break;
    }
    int tmp = heap[parent];
    heap[parent] = heap[child];
    heap[child] = tmp;

    child = parent;
  }

  
}

void build(int *heap, int n)
/*@ With (input : list Z)
    Require
      0 <= n &&
      n <= heap_capacity &&
      Zlength(input) == n &&
      IntArray::full(heap, n, input)
    Ensure
      store_heap(heap, list_to_multiset(input), n)
 */
{

  for (int i = 1; i < n; ++i) {
    int x = heap[i];

    push(heap, i, x);

    
  }

}

int pop(int *heap, int n)
/*@ With (S_before : multiset Z)
    Require
      1 <= n &&
      store_heap(heap, S_before, n)
    Ensure
      __return == multiset_max(S_before) &&
      multiset_maximum(S_before, __return) &&
      store_heap(
        heap,
        multiset_remove(S_before, multiset_max(S_before)),
        n - 1
      ) *
      IntArray::undef_seg(heap, n - 1, n)
 */
{

  int ret = heap[0];

  if (n == 1) {

    return ret;
  }

  heap[0] = heap[n - 1];

  int idx = 0;

  while (idx * 2 + 1 < n - 1) {
    int left = idx * 2 + 1;
    int right = left + 1;
    int largest = left;

    if (right < n - 1 && heap[left] < heap[right]) {
      largest = right;
    }

    if (heap[idx] >= heap[largest]) {

      break;
    }
    int tmp = heap[idx];
    heap[idx] = heap[largest];
    heap[largest] = tmp;

    idx = largest;
  }

  

  return ret;
}

void heap_sort(int *heap, int n)
/*@ With (input : list Z)
    Require
      0 <= n &&
      n <= heap_capacity &&
      Zlength(input) == n &&
      IntArray::full(heap, n, input)
    Ensure
      exists output,
        Zlength(output) == n &&
        Permutation(input, output) &&
        increasing(output) &&
        IntArray::full(heap, n, output)
 */
{
  build(heap, n);

  int i = n;

  while (i > 0) {

    int extracted = pop(heap, i);

    heap[i - 1] = extracted;

    --i;

  }

}
