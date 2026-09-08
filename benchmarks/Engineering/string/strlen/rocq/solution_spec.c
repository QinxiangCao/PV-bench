#include "../../string.h"

int strlen(char *s)
/*@ With str
    Require valid_string(str) && string_length(str) < INT_MAX && store_string(s, str)
    Ensure __return == string_length(str) && store_string(s, str)
*/
{
  int i = 0;

  while (s[i] != 0) {
    i++;
  }
  return i;
}

