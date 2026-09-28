# 886/D — Restoration of string

*Rating:* 2000 · *Limits:* 2.0s, 256.0 MB · *Tags:* constructive algorithms, graphs, implementation

## Description

A substring of some string is called the most frequent, if the number of its occurrences is not less than number of occurrences of any other substring.

You are given a set of strings. A string (not necessarily from this set) is called good if all elements of the set are the most frequent substrings of this string. Restore the non-empty good string with minimum length. If several such strings exist, restore lexicographically minimum string. If there are no good strings, print "NO" (without quotes).

A substring of a string is a contiguous subsequence of letters in the string. For example, "ab", "c", "abc" are substrings of string "abc", while "ac" is not a substring of that string.

The number of occurrences of a substring in a string is the number of starting positions in the string where the substring occurs. These occurrences could overlap.

String a is lexicographically smaller than string b, if a is a prefix of b, or a has a smaller letter at the first position where a and b differ.

## Input

The first line contains integer n (1 ≤ n ≤ 105) — the number of strings in the set.

Each of the next n lines contains a non-empty string consisting of lowercase English letters. It is guaranteed that the strings are distinct.

The total length of the strings doesn't exceed 105.

## Output

Print the non-empty good string with minimum length. If several good strings exist, print lexicographically minimum among them. Print "NO" (without quotes) if there are no good strings.

## Note

One can show that in the first sample only two good strings with minimum length exist: "cfmailru" and "mailrucf". The first string is lexicographically minimum.

## Examples

*Example 1 — input:*
```
4
mail
ai
lru
cf
```

*Example 1 — output:*
```
cfmailru
```

*Example 2 — input:*
```
3
kek
preceq
cheburek
```

*Example 2 — output:*
```
NO
```
