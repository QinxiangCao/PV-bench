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

char *strchr(char *s, int c)

{
  int i = 0;

  while (s[i] != 0) {
    if (s[i] == c) {
      return s + i;
    }
    i++;
  }
  if (c == 0) {
    return s + i;
  }
  return (void *)0;
}

