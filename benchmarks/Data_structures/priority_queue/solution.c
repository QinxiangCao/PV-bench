void push(int *heap, int n, int x)

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

{

  for (int i = 1; i < n; ++i) {
    int x = heap[i];

    push(heap, i, x);

    
  }

}

int pop(int *heap, int n)

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

{
  build(heap, n);

  int i = n;

  while (i > 0) {

    int extracted = pop(heap, i);

    heap[i - 1] = extracted;

    --i;

  }

}
