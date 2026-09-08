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
  /*@ Inv Assert
      all_ascii(bytes) && Zlength(bytes) == n@pre &&
      0 <= n@pre && n@pre < INT_MAX &&
      0 <= i && i <= n@pre &&
      dest == dest@pre && src == src@pre && n == n@pre &&
      CharArray::full(dest@pre, i, sublist(0, i, bytes)) *
      CharArray::undef_seg(dest@pre, i, n@pre) *
      CharArray::full(src@pre, n@pre, bytes)
  */
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
    /*@ Inv Assert
        all_ascii(bytes) && Zlength(bytes) == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        0 <= i && i <= n@pre &&
        dest == dest@pre && src == src@pre && n == n@pre &&
        CharArray::full(dest@pre, i, sublist(0, i, bytes)) *
        CharArray::undef_seg(dest@pre, i, n@pre) *
        CharArray::full(src@pre, n@pre, bytes)
    */
    while (i < n) {
      dest[i] = src[i];
      i++;
    }
  } else {
    int i = n;
    /*@ Inv Assert
        all_ascii(bytes) && Zlength(bytes) == n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        0 <= i && i <= n@pre &&
        dest == dest@pre && src == src@pre && n == n@pre &&
        CharArray::undef_seg(dest@pre, 0, i) *
        CharArray::full(dest@pre + i * sizeof(char), n@pre - i,
                        sublist(i, n@pre, bytes)) *
        CharArray::full(src@pre, n@pre, bytes)
    */
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
  /*@ Inv Assert
      0 <= n@pre && n@pre < INT_MAX &&
      0 <= c@pre && c@pre <= 127 &&
      0 <= i && i <= n@pre &&
      s == s@pre && c == c@pre && n == n@pre &&
      CharArray::full(s@pre, i, repeat_Z(c@pre, i)) *
      CharArray::undef_seg(s@pre, i, n@pre)
  */
  while (i < n) {
    s[i] = c;
    i++;
  }
  return s;
}

