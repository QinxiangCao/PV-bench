# 1891/A — Sorting with Twos

*Rating:* 800 · *Limits:* 2.0s, 256.0 MB · *Tags:* constructive algorithms, sortings

## Description

You are given an array of integers $a_1, a_2, \ldots, a_n$. In one operation, you do the following:

- Choose a non-negative integer $m$, such that $2^m \leq n$.
- Subtract $1$ from $a_i$ for all integers $i$, such that $1 \leq i \leq 2^m$.

Can you sort the array in non-decreasing order by performing some number (possibly zero) of operations?

An array is considered non-decreasing if $a_i \leq a_{i + 1}$ for all integers $i$ such that $1 \leq i \leq n - 1$.

## Input

The first line contains a single integer $t$ ($1 \leq t \leq 10^4$) — the number of test cases. The description of the test cases follows.

The first line of each test case contains a single integer $n$ ($1 \leq n \leq 20$) — the length of array $a$.

The second line of each test case contains $n$ integers $a_1, a_2, \ldots, a_n$ — the integers in array $a$ ($0 \leq a_i \leq 1000$).

## Output

For each test case, output "YES" if the array can be sorted, and "NO" otherwise.

## Note

In the first test case, the array is already sorted in non-decreasing order, so we don't have to perform any operations.

In the second test case, we can choose $m = 1$ twice to get the array $[4, 3, 3, 4, 4]$. Then, we can choose $m = 0$ once and get the sorted in non-decreasing order array $[3, 3, 3, 4, 4]$.

In the third test case, we can choose $m = 0$ once and get the array $[5, 5, 5, 7, 5, 6, 6, 8, 7]$. Then, we can choose $m = 2$ twice and get the array $[3, 3, 3, 5, 5, 6, 6, 8, 7]$. After that, we can choose $m = 3$ once and get the sorted in non-decreasing order array $[2, 2, 2, 4, 4, 5, 5, 7, 7]$.

For the fourth and fifth test case, it can be shown that the array could not be sorted using these operations.

## Examples

*Example 1 — input:*
```
8
5
1 2 3 4 5
5
6 5 3 4 4
9
6 5 5 7 5 6 6 8 7
4
4 3 2 1
6
2 2 4 5 3 2
8
1 3 17 19 27 57 179 13
5
3 17 57 179 92
10
1 2 3 4 0 6 7 8 9 10
```

*Example 1 — output:*
```
YES
YES
YES
NO
NO
NO
YES
YES
```
