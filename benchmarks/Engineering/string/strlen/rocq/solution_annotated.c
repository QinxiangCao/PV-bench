#include "../../string.h"

int strlen(char *s)
/*@ With str
    Require valid_string(str) && string_length(str) < INT_MAX && store_string(s, str)
    Ensure __return == string_length(str) && store_string(s, str)
*/
{
  int i = 0;
  /*@ Inv Assert
      valid_string(str) &&
      string_length(str) < INT_MAX &&
      0 <= i && i <= string_length(str) &&
      s == s@pre &&
      (forall (k: Z), (0 <= k && k < i) => Znth(k, str, 0) != 0) &&
      store_string(s@pre, str)
  */
  while (s[i] != 0) {
    i++;
  }
  return i;
}

