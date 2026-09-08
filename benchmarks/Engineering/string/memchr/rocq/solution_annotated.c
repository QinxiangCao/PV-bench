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
  /*@ Inv Assert
      all_ascii(bytes) && Zlength(bytes) == n@pre &&
      0 <= c@pre && c@pre <= 127 &&
      0 <= n@pre && n@pre < INT_MAX &&
      0 <= i && i <= n@pre &&
      s == s@pre && c == c@pre && n == n@pre &&
      (forall (k: Z), (0 <= k && k < i) => Znth(k, bytes, 0) != c@pre) &&
      CharArray::full(s@pre, n@pre, bytes)
  */
  while (i < n) {
    if (s[i] == c) {
      return s + i;
    }
    i++;
  }
  return (void *)0;
}

