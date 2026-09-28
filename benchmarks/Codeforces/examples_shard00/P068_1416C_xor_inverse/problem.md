# 1416/C — XOR Inverse

*Rating:* 2000 · *Limits:* 2.0s, 512.0 MB · *Tags:* bitmasks, data structures, divide and conquer, dp, greedy, math, sortings, strings, trees

## Description

You are given an array $a$ consisting of $n$ non-negative integers. You have to choose a non-negative integer $x$ and form a new array $b$ of size $n$ according to the following rule: for all $i$ from $1$ to $n$, $b_i = a_i \oplus x$ ($\oplus$ denotes the operation bitwise XOR).

An inversion in the $b$ array is a pair of integers $i$ and $j$ such that $1 \le i < j \le n$ and $b_i > b_j$.

You should choose $x$ in such a way that the number of inversions in $b$ is minimized. If there are several options for $x$ — output the smallest one.

## Input

First line contains a single integer $n$ ($1 \le n \le 3 \cdot 10^5$) — the number of elements in $a$.

Second line contains $n$ space-separated integers $a_1$, $a_2$, ..., $a_n$ ($0 \le a_i \le 10^9$), where $a_i$ is the $i$-th element of $a$.

## Output

Output two integers: the minimum possible number of inversions in $b$, and the minimum possible value of $x$, which achieves those number of inversions.

## Note

In the first sample it is optimal to leave the array as it is by choosing $x = 0$.

In the second sample the selection of $x = 14$ results in $b$: $[4, 9, 7, 4, 9, 11, 11, 13, 11]$. It has $4$ inversions:

- $i = 2$, $j = 3$;
- $i = 2$, $j = 4$;
- $i = 3$, $j = 4$;
- $i = 8$, $j = 9$.

In the third sample the selection of $x = 8$ results in $b$: $[0, 2, 11]$. It has no inversions.

## Examples

*Example 1 — input:*
```
4
0 1 3 2
```

*Example 1 — output:*
```
1 0
```

*Example 2 — input:*
```
9
10 7 9 10 7 5 5 3 5
```

*Example 2 — output:*
```
4 14
```

*Example 3 — input:*
```
3
8 10 3
```

*Example 3 — output:*
```
0 8
```
