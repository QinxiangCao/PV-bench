int lowbit(int x)

{
  return x & (-x);
}

void add(int *bit, int n, int pos, int delta)

{

  while (pos <= n) {
    bit[pos] += delta;
    pos += lowbit(pos);
  }
}

int query(int *bit, int pos)

{
  int sum = 0;

  while (pos > 0) {
    sum += bit[pos];
    pos -= lowbit(pos);
  }

  return sum;
}

