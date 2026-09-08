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

char *strchr(char *s, int c)
/*@ With str
    Require valid_string(str) &&
            0 <= c && c <= 127 &&
            string_length(str) < INT_MAX &&
            store_string(s, str)
    Ensure strchr_result(str, c, __return, s) && store_string(s, str)
*/
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

