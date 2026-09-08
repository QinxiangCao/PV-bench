#include "../../string.h"

char *strcat(char *dest, char *src)
/*@ With dst_str src_str
    Require valid_string(dst_str) && valid_string(src_str) &&
            string_length(dst_str) + string_length(src_str) + 1 < INT_MAX &&
            store_string(dest, dst_str) *
            CharArray::undef_seg(dest, string_length(dst_str) + 1,
                                      string_length(dst_str) + string_length(src_str) + 1) *
            store_string(src, src_str)
    Ensure __return == dest &&
           store_string(dest, app(dst_str, src_str)) *
           store_string(src, src_str)
*/
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
/*@ With dst_str src_str
    Require valid_string(dst_str) && valid_string(src_str) &&
            0 <= n && n < INT_MAX &&
            string_length(dst_str) + n + 1 < INT_MAX &&
            store_string(dest, dst_str) *
            CharArray::undef_seg(dest, string_length(dst_str) + 1,
                                      string_length(dst_str) + n + 1) *
            store_string(src, src_str)
    Ensure exists out,
             strncat_result(dst_str, src_str, n, out) &&
             __return == dest &&
             store_string(dest, out) *
             CharArray::undef_seg(dest, string_length(out) + 1,
                                  string_length(dst_str) + n + 1) *
             store_string(src, src_str)
*/
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

