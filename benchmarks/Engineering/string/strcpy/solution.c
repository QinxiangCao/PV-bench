char *strcpy(char *dest, char *src)

{
  int i = 0;

  while (src[i] != 0) {
    dest[i] = src[i];
    i++;
  }
  dest[i] = 0;
  return dest;
}

char *strncpy(char *dest, char *src, int n)

{
  int i = 0;

  while (i < n && src[i] != 0) {
    dest[i] = src[i];
    i++;
  }

  while (i < n) {
    dest[i] = 0;
    i++;
  }
  return dest;
}

