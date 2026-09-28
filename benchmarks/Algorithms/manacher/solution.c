#include "string.h"

int longestPalindrom(char *s, int n, char *output)

{
    int i = 0;
    int j = 0;
    int len = 0;
    int id = 0;
    int limit = 0;
    int maxLen = 0;
    int maxId = 0;
    int r = 0;
    int mirror = 0;
    int ret = 0;
    char s2[2003];
    int p[2003];
    p[0] = 0;
    s2[0] = 36;

    while (i < n) {
        s2[2 * i + 1] = 35;
        s2[2 * i + 2] = s[i];
        i++;
    }
    s2[2 * i + 1] = 35;
    len = 2 * i + 2;
    s2[len] = 0;
    id = 0;
    limit = 0;
    maxLen = 0;
    maxId = 0;
    i = 1;

    while (i < len) {
        if (i < limit) {
            mirror = 2 * id - i;

            if (p[mirror] < limit - i) {
                r = p[mirror];
                p[i] = r;
            } else {
                r = limit - i;
                p[i] = r;
            }
        } else {
            r = 1;
            p[i] = r;
        }

        while (s2[i + r] == s2[i - r]) {

            r++;
            p[i] = r;
        }
        if (i + r > limit) {
            limit = i + r;
            id = i;
        }
        r = r - 1;
        if (maxLen < r) {
            maxLen = r;
            maxId = i;
        }
        r = 0;
        mirror = 0;
        i++;
    }
    j = 0;
    i = maxId - maxLen;

    while (i <= maxId + maxLen) {
        if (s2[i] != 35) {
            output[j] = s2[i];
            j++;
        }
        i++;
    }

    output[j] = 0;
    ret = maxLen;
    return ret;
}
