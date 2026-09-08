#include "../../string.h"

char *strcpy(char *dest, char *src)
/*@ With src_str
    Require valid_string(src_str) &&
            string_length(src_str) < INT_MAX &&
            CharArray::undef_full(dest, string_length(src_str) + 1) *
            store_string(src, src_str)
    Ensure __return == dest &&
           store_string(dest, src_str) * store_string(src, src_str)
*/
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
/*@ With src_str
    Require valid_string(src_str) &&
            0 <= n && n < INT_MAX &&
            CharArray::undef_full(dest, n) *
            store_string(src, src_str)
    Ensure exists out,
             strncpy_content(src_str, n, out) &&
             __return == dest &&
             CharArray::full(dest, n, out) * store_string(src, src_str)
*/
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

