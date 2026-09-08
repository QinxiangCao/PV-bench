char *memchr(char *s, int c, int n)

{
  int i = 0;

  while (i < n) {
    if (s[i] == c) {
      return s + i;
    }
    i++;
  }
  return (void *)0;
}

