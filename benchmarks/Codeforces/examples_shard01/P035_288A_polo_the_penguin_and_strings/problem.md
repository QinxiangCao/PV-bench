# 288/A — Polo the Penguin and Strings

*Rating:* 1300 · *Limits:* 2.0s, 256.0 MB · *Tags:* greedy

## Description

Little penguin Polo adores strings. But most of all he adores strings of length $n$.

One day he wanted to find a string that meets the following conditions:

1. The string consists of $n$ lowercase English letters (that is, the string's length equals $n$), exactly $k$ of these letters are distinct.
2. No two neighbouring letters of a string coincide; that is, if we represent a string as $s = s_1s_2\ldots s_n$, then the following inequality holds, $s_i \ne s_{i+1}$ ($1 \le i < n$).
3. Among all strings that meet points 1 and 2, the required string is lexicographically smallest.

Help him find such string or state that such string doesn't exist.

String $x = x_1x_2\ldots x_p$ is lexicographically less than string $y = y_1y_2\ldots y_q$, if either $p < q$ and $x_1 = y_1$, $x_2 = y_2$, $\ldots$, $x_p = y_p$, or there is such number $r$ ($r < p$, $r < q$), that $x_1 = y_1$, $x_2 = y_2$, $\ldots$, $x_r = y_r$ and $x_{r+1} < y_{r+1}$. The characters of the strings are compared by their ASCII codes.

## Input

A single line contains two positive integers $n$ and $k$ ($1 \le n \le 10^6$, $1 \le k \le 26$) — the string's length and the number of distinct letters.

## Output

In a single line print the required string. If there isn't such string, print "-1" (without the quotes).

## Examples

*Example 1 — input:*
```
7 4
```
*Example 1 — output:*
```
ababacd
```

*Example 2 — input:*
```
4 7
```
*Example 2 — output:*
```
-1
```
