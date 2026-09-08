#include "../../string.h"

char *memchr(char *s, int c, int n)
/*@ With bytes
    Require all_ascii(bytes) && Zlength(bytes) == n &&
            0 <= c && c <= 127 &&
            0 <= n && n < INT_MAX &&
            CharArray::full(s, n, bytes)
    Ensure memchr_result(bytes, c, n, __return, s) &&
           CharArray::full(s, n, bytes)
*/
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

