char *strcat(char *dest, char *src)

{
  int i = 0;

  while (dest[i] != 0) {
    i++;
  }

  int j = 0;

  while (src[j] != 0) {

    dest[i + j] = src[j];
    j++;
    dest[i + j] = 0;
  }
  return dest;
}

char *strncat(char *dest, char *src, int n)

{
  int i = 0;

  while (dest[i] != 0) {
    i++;
  }

  int j = 0;

  while (j < n && src[j] != 0) {

    dest[i + j] = src[j];
    j++;
    dest[i + j] = 0;
  }
  return dest;
}

