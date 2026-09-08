char *memcpy(char *dest, char *src, int n)

{
  int i = 0;

  while (i < n) {
    dest[i] = src[i];
    i++;
  }
  return dest;
}

char *memmove(char *dest, char *src, int n)

{
  if (dest < src) {
    int i = 0;

    while (i < n) {
      dest[i] = src[i];
      i++;
    }
  } else {
    int i = n;

    while (i > 0) {
      i--;
      dest[i] = src[i];
    }
  }
  return dest;
}

char *memset(char *s, int c, int n)

{
  int i = 0;

  while (i < n) {
    s[i] = c;
    i++;
  }
  return s;
}

