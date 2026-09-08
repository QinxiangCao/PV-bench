#include "../../string.h"

char *memcpy(char *dest, char *src, int n)
/*@ With bytes
    Require all_ascii(bytes) && Zlength(bytes) == n &&
            0 <= n && n < INT_MAX &&
            CharArray::undef_full(dest, n) * CharArray::full(src, n, bytes)
    Ensure __return == dest &&
           CharArray::full(dest, n, bytes) * CharArray::full(src, n, bytes)
*/
{
  int i = 0;

  while (i < n) {
    dest[i] = src[i];
    i++;
  }
  return dest;
}

char *memmove(char *dest, char *src, int n)
/*@ With bytes
    Require all_ascii(bytes) && Zlength(bytes) == n &&
            0 <= n && n < INT_MAX &&
            CharArray::undef_full(dest, n) * CharArray::full(src, n, bytes)
    Ensure __return == dest &&
           CharArray::full(dest, n, bytes) * CharArray::full(src, n, bytes)
*/
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
/*@ Require 0 <= n && n < INT_MAX &&
            0 <= c && c <= 127 &&
            CharArray::undef_full(s, n)
    Ensure __return == s && CharArray::full(s, n, repeat_Z(c, n))
*/
{
  int i = 0;

  while (i < n) {
    s[i] = c;
    i++;
  }
  return s;
}

