void push(int *stack, int n, int x)

{

  stack[n] = x;

}

int pop(int *stack, int n)

{

  int ret = stack[n - 1];

  return ret;
}

void build(int *stack, int n)

{

  for (int i = 1; i < n; ++i) {
    int x = stack[i];

    push(stack, i, x);

  }

}

