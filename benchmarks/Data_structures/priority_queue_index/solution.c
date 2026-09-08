void push(int *key, int *data, int n, int data_x, int key_x)

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

