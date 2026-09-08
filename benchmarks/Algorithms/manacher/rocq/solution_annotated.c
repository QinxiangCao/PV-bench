#include "string.h"

/*@ Extern Coq
      (AlnumString : list Z -> Prop)
      (LongestPalindromeResult : list Z -> list Z -> Z -> Prop)
      (ManacherTransformedPrefix : list Z -> list Z -> Z -> Prop)
      (ManacherTransformedString : list Z -> list Z -> Z -> Prop)
      (RadiusTablePrefix : list Z -> Z -> list Z -> Z -> Prop)
      (CurrentRightmostWindow : list Z -> Z -> Z -> Z -> Prop)
      (BestRadiusPrefix : list Z -> Z -> list Z -> Z -> Z -> Prop)
      (ManacherLoopState : list Z -> list Z -> Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (ExpansionLoopState : list Z -> list Z -> Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (ExpansionCandidate : list Z -> Z -> Z -> Z -> Prop)
      (ExpansionAfterMatch : list Z -> Z -> Z -> Z -> Prop)
      (OutputCopyPrefix : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (OutputCopyBound : list Z -> Z -> Z -> Z -> Prop)
      (OutputCopyDone : list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.manacher.rocq.spec_lib */
/*@ Import Coq Require Import PVbench.Algorithms.manacher.rocq.helper_lib */

int longestPalindrom(char *s, int n, char *output)
/*@ With (str : list Z)
    Require
      valid_string(str) &&
      AlnumString(str) &&
      string_length(str) == n &&
      1 <= n && n <= 1000 &&
      store_string(s, str) *
      CharArray::undef_full(output, n + 1)
    Ensure
      exists out,
      LongestPalindromeResult(str, out, __return) &&
      1 <= __return && __return <= n &&
      store_string(s, str) *
      CharArray::full(output, __return + 1, app(out, cons(0, nil))) *
      CharArray::undef_seg(output, __return + 1, n + 1)
 */
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
    /*@ Inv Assert
        exists s2_pre p_pre,
        valid_string(str) &&
        AlnumString(str) &&
        string_length(str) == n@pre &&
        1 <= n@pre && n@pre <= 1000 &&
        0 <= i && i <= n@pre &&
        s == s@pre && output == output@pre && n == n@pre &&
        j == 0 && len == 0 && id == 0 && limit == 0 &&
        maxLen == 0 && maxId == 0 && r == 0 && mirror == 0 && ret == 0 &&
        Zlength(s2_pre) == 2 * i + 1 &&
        Zlength(p_pre) == 1 &&
        ManacherTransformedPrefix(str, s2_pre, i) &&
        store_string(s@pre, str) *
        CharArray::undef_full(output@pre, n@pre + 1) *
        CharArray::seg(s2, 0, 2 * i + 1, s2_pre) *
        CharArray::undef_seg(s2, 2 * i + 1, 2003) *
        IntArray::seg(p, 0, 1, p_pre) *
        IntArray::undef_seg(p, 1, 2003)
    */
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
    /*@ Assert
        exists s2_full p_pre,
        valid_string(str) &&
        AlnumString(str) &&
        string_length(str) == n@pre &&
        1 <= n@pre && n@pre <= 1000 &&
        len == 2 * n@pre + 2 &&
        len <= 2002 &&
        i == 1 && id == 0 && limit == 0 && maxLen == 0 && maxId == 0 &&
        j == 0 && r == 0 && mirror == 0 && ret == 0 &&
        s == s@pre && output == output@pre && n == n@pre &&
        Zlength(s2_full) == len + 1 &&
        Zlength(p_pre) == 1 &&
        ManacherTransformedString(str, s2_full, len) &&
        store_string(s@pre, str) *
        CharArray::undef_full(output@pre, n@pre + 1) *
        CharArray::seg(s2, 0, len + 1, s2_full) *
        CharArray::undef_seg(s2, len + 1, 2003) *
        IntArray::seg(p, 0, 1, p_pre) *
        IntArray::undef_seg(p, 1, 2003)
     */
    /*@ Inv Assert
        exists s2_full p_cur,
        valid_string(str) &&
        AlnumString(str) &&
        string_length(str) == n@pre &&
        1 <= n@pre && n@pre <= 1000 &&
        len == 2 * n@pre + 2 &&
        len <= 2002 &&
        1 <= i && i <= len &&
        j == 0 && r == 0 && mirror == 0 && ret == 0 &&
        0 <= id && id < len &&
        0 <= limit && limit <= len &&
        0 <= maxLen && maxLen <= n@pre &&
        0 <= maxId && maxId < len &&
        s == s@pre && output == output@pre && n == n@pre &&
        Zlength(s2_full) == len + 1 &&
        Zlength(p_cur) == i &&
        ManacherLoopState(str, s2_full, len, p_cur, i, id, limit, maxId, maxLen) &&
        store_string(s@pre, str) *
        CharArray::undef_full(output@pre, n@pre + 1) *
        CharArray::seg(s2, 0, len + 1, s2_full) *
        CharArray::undef_seg(s2, len + 1, 2003) *
        IntArray::seg(p, 0, i, p_cur) *
        IntArray::undef_seg(p, i, 2003)
     */
    while (i < len) {
        if (i < limit) {
            mirror = 2 * id - i;
            /*@ Assert
                exists s2_full p_cur,
                valid_string(str) &&
                AlnumString(str) &&
                string_length(str) == n@pre &&
                1 <= n@pre && n@pre <= 1000 &&
                len == 2 * n@pre + 2 &&
                len <= 2002 &&
                1 <= i && i < len &&
                0 <= mirror && mirror < i &&
                mirror == 2 * id - i &&
                j == 0 && r == 0 && ret == 0 &&
                i < limit && limit <= len &&
                s == s@pre && output == output@pre && n == n@pre &&
                Zlength(s2_full) == len + 1 &&
                Zlength(p_cur) == i &&
                ManacherLoopState(str, s2_full, len, p_cur, i, id, limit, maxId, maxLen) &&
                store_string(s@pre, str) *
                CharArray::undef_full(output@pre, n@pre + 1) *
                CharArray::seg(s2, 0, len + 1, s2_full) *
                CharArray::undef_seg(s2, len + 1, 2003) *
                IntArray::seg(p, 0, i, p_cur) *
                IntArray::undef_seg(p, i, 2003)
             */
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
        /*@ Assert
            exists s2_full p_written,
            valid_string(str) &&
            AlnumString(str) &&
            string_length(str) == n@pre &&
            1 <= n@pre && n@pre <= 1000 &&
            len == 2 * n@pre + 2 &&
            len <= 2002 &&
            1 <= i && i < len &&
            j == 0 && ret == 0 &&
            1 <= r &&
            0 <= id && id < len &&
            0 <= limit && limit <= len &&
            0 <= mirror && mirror < len &&
            0 <= maxLen && maxLen <= n@pre &&
            0 <= maxId && maxId < len &&
            0 <= i - r && i + r <= len &&
            s == s@pre && output == output@pre && n == n@pre &&
            Zlength(s2_full) == len + 1 &&
            Zlength(p_written) == i + 1 &&
            ExpansionLoopState(str, s2_full, len, p_written, i, r, id, limit, maxId, maxLen) &&
            ExpansionCandidate(s2_full, len, i, r) &&
            store_string(s@pre, str) *
            CharArray::undef_full(output@pre, n@pre + 1) *
            CharArray::seg(s2, 0, len + 1, s2_full) *
            CharArray::undef_seg(s2, len + 1, 2003) *
            IntArray::seg(p, 0, i + 1, p_written) *
            IntArray::undef_seg(p, i + 1, 2003)
         */
        /*@ Inv Assert
            exists s2_full p_written,
            valid_string(str) &&
            AlnumString(str) &&
            string_length(str) == n@pre &&
            1 <= n@pre && n@pre <= 1000 &&
            len == 2 * n@pre + 2 &&
            len <= 2002 &&
            1 <= i && i < len &&
            j == 0 && ret == 0 &&
            1 <= r &&
            0 <= id && id < len &&
            0 <= limit && limit <= len &&
            0 <= mirror && mirror < len &&
            0 <= maxLen && maxLen <= n@pre &&
            0 <= maxId && maxId < len &&
            0 <= i - r && i + r <= len &&
            s == s@pre && output == output@pre && n == n@pre &&
            Zlength(s2_full) == len + 1 &&
            Zlength(p_written) == i + 1 &&
            ExpansionLoopState(str, s2_full, len, p_written, i, r, id, limit, maxId, maxLen) &&
            ExpansionCandidate(s2_full, len, i, r) &&
            store_string(s@pre, str) *
            CharArray::undef_full(output@pre, n@pre + 1) *
            CharArray::seg(s2, 0, len + 1, s2_full) *
            CharArray::undef_seg(s2, len + 1, 2003) *
            IntArray::seg(p, 0, i + 1, p_written) *
            IntArray::undef_seg(p, i + 1, 2003)
         */
        while (s2[i + r] == s2[i - r]) {
            /*@ Assert
                exists s2_full p_written,
                valid_string(str) &&
                AlnumString(str) &&
                string_length(str) == n@pre &&
                1 <= n@pre && n@pre <= 1000 &&
                len == 2 * n@pre + 2 &&
                len <= 2002 &&
                1 <= i && i < len &&
                j == 0 && ret == 0 &&
                1 <= r &&
                0 <= id && id < len &&
                0 <= limit && limit <= len &&
                0 <= mirror && mirror < len &&
                0 <= maxLen && maxLen <= n@pre &&
                0 <= maxId && maxId < len &&
                0 < i - r && i + r < len &&
                s == s@pre && output == output@pre && n == n@pre &&
                Zlength(s2_full) == len + 1 &&
                Zlength(p_written) == i + 1 &&
                ExpansionLoopState(str, s2_full, len, p_written, i, r, id, limit, maxId, maxLen) &&
                ExpansionAfterMatch(s2_full, len, i, r) &&
                store_string(s@pre, str) *
                CharArray::undef_full(output@pre, n@pre + 1) *
                CharArray::seg(s2, 0, len + 1, s2_full) *
                CharArray::undef_seg(s2, len + 1, 2003) *
                IntArray::seg(p, 0, i + 1, p_written) *
                IntArray::undef_seg(p, i + 1, 2003)
             */
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
        /*@ Assert
            exists s2_full p_next,
            valid_string(str) &&
            AlnumString(str) &&
            string_length(str) == n@pre &&
            1 <= n@pre && n@pre <= 1000 &&
            len == 2 * n@pre + 2 &&
            len <= 2002 &&
            1 <= i && i <= len &&
            j == 0 && r == 0 && mirror == 0 && ret == 0 &&
            0 <= maxLen && maxLen <= n@pre &&
            0 <= maxId && maxId < len &&
            s == s@pre && output == output@pre && n == n@pre &&
            Zlength(s2_full) == len + 1 &&
            Zlength(p_next) == i &&
            ManacherLoopState(str, s2_full, len, p_next, i, id, limit, maxId, maxLen) &&
            store_string(s@pre, str) *
            CharArray::undef_full(output@pre, n@pre + 1) *
            CharArray::seg(s2, 0, len + 1, s2_full) *
            CharArray::undef_seg(s2, len + 1, 2003) *
            IntArray::seg(p, 0, i, p_next) *
            IntArray::undef_seg(p, i, 2003)
         */
    }
    j = 0;
    i = maxId - maxLen;
    /*@ Assert
        exists s2_full p_done out_pre,
        valid_string(str) &&
        AlnumString(str) &&
        string_length(str) == n@pre &&
        1 <= n@pre && n@pre <= 1000 &&
        len == 2 * n@pre + 2 &&
        len <= 2002 &&
        1 <= maxLen &&
        0 <= maxLen && maxLen <= n@pre &&
        0 <= maxId - maxLen && maxId + maxLen < len &&
        i == maxId - maxLen &&
        j == 0 &&
        r == 0 && mirror == 0 && ret == 0 &&
        out_pre == nil &&
        OutputCopyPrefix(s2_full, out_pre, maxId - maxLen, i, j) &&
        (forall (cur : Z), (maxId - maxLen <= cur && cur <= maxId + maxLen + 1) =>
            OutputCopyBound(s2_full, maxId - maxLen, cur, maxLen)) &&
        s == s@pre && output == output@pre && n == n@pre &&
        Zlength(s2_full) == len + 1 &&
        Zlength(p_done) == len &&
        ManacherLoopState(str, s2_full, len, p_done, len, id, limit, maxId, maxLen) &&
        store_string(s@pre, str) *
        CharArray::undef_full(output@pre, n@pre + 1) *
        CharArray::seg(s2, 0, len + 1, s2_full) *
        CharArray::undef_seg(s2, len + 1, 2003) *
        IntArray::seg(p, 0, len, p_done) *
        IntArray::undef_seg(p, len, 2003)
     */
    /*@ Inv Assert
        exists s2_full p_done out_prefix,
        valid_string(str) &&
        AlnumString(str) &&
        string_length(str) == n@pre &&
        1 <= n@pre && n@pre <= 1000 &&
        len == 2 * n@pre + 2 &&
        len <= 2002 &&
        1 <= maxLen &&
        0 <= maxLen && maxLen <= n@pre &&
        0 <= maxId - maxLen && maxId + maxLen < len &&
        maxId - maxLen <= i && i <= maxId + maxLen + 1 &&
        0 <= j && j <= maxLen &&
        r == 0 && mirror == 0 && ret == 0 &&
        OutputCopyPrefix(s2_full, out_prefix, maxId - maxLen, i, j) &&
        (forall (cur : Z), (maxId - maxLen <= cur && cur <= maxId + maxLen + 1) =>
            OutputCopyBound(s2_full, maxId - maxLen, cur, maxLen)) &&
        s == s@pre && output == output@pre && n == n@pre &&
        Zlength(s2_full) == len + 1 &&
        Zlength(p_done) == len &&
        ManacherLoopState(str, s2_full, len, p_done, len, id, limit, maxId, maxLen) &&
        store_string(s@pre, str) *
        CharArray::full(output@pre, j, out_prefix) *
        CharArray::undef_seg(output@pre, j, n@pre + 1) *
        CharArray::seg(s2, 0, len + 1, s2_full) *
        CharArray::undef_seg(s2, len + 1, 2003) *
        IntArray::seg(p, 0, len, p_done) *
        IntArray::undef_seg(p, len, 2003)
     */
    while (i <= maxId + maxLen) {
        if (s2[i] != 35) {
            output[j] = s2[i];
            j++;
        }
        i++;
    }
    output[j] = 0;
    ret = maxLen;
    /*@ Assert
        exists (s2_full : list Z) (p_done : list Z) (out : list Z),
        valid_string(str) &&
        AlnumString(str) &&
        string_length(str) == n@pre &&
        1 <= n@pre && n@pre <= 1000 &&
        len == 2 * n@pre + 2 &&
        ret == maxLen &&
        i == maxId + maxLen + 1 &&
        j == ret &&
        0 <= id && id < len &&
        0 <= limit && limit <= len &&
        0 <= maxId && maxId < len &&
        1 <= maxLen &&
        0 <= maxLen && maxLen <= n@pre &&
        r == 0 && mirror == 0 &&
        1 <= ret && ret <= n@pre &&
        OutputCopyDone(str, s2_full, out, len, maxId, maxLen, ret) &&
        LongestPalindromeResult(str, out, ret) &&
        s == s@pre && output == output@pre && n == n@pre &&
        Zlength(s2_full) == len + 1 &&
        Zlength(p_done) == len &&
        store_string(s@pre, str) *
        CharArray::full(output@pre, ret + 1, app(out, cons(0, nil))) *
        CharArray::undef_seg(output@pre, ret + 1, n@pre + 1) *
        CharArray::undef_full(s2, 2003) *
        IntArray::undef_full(p, 2003)
     */
    return ret;
}
