# 1800/D — Remove Two Letters

*Rating:* 1200 · *Limits:* 2.0s, 256.0 MB · *Tags:* data structures, greedy, hashing, strings

## Description

Dmitry has a string $s$, consisting of lowercase Latin letters.

Dmitry decided to remove two consecutive characters from the string $s$ and you are wondering how many different strings can be obtained after such an operation.

For example, Dmitry has a string "aaabcc". You can get the following different strings: "abcc"(by deleting the first two or second and third characters), "aacc"(by deleting the third and fourth characters),"aaac"(by deleting the fourth and the fifth character) and "aaab" (by deleting the last two).

## Input

The first line of input data contains a single integer $t$ ($1 \le t \le 10^4$) — number of test cases.

The descriptions of the test cases follow.

The first line of the description of each test case contains an integer $n$ ($3 \le n \le 2 \cdot 10^5$).

The second line of the description of each test case contains a string $s$ of length $n$ consisting of lowercase Latin letters.

It is guaranteed that the sum of $n$ for all test cases does not exceed $2 \cdot 10^5$.

## Output

For each test case print one integer — the number of distinct strings that can be obtained by removing two consecutive letters.

## Note

The first example is explained in the statement.

In the third example, the following strings are obtained: "cdef", "adef", "abef", "abcf", "abcd".

In the seventh example, any deletion will result in the string "aba".

## Examples

*Example 1 — input:*
```
7
6
aaabcc
10
aaaaaaaaaa
6
abcdef
7
abacaba
6
cccfff
4
abba
5
ababa
```

*Example 1 — output:*
```
4
1
5
3
3
3
1
```
