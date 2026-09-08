# 1288/D — Minimax Problem

*Rating:* 2000 · *Limits:* 5.0s, 512.0 MB · *Tags:* binary search, bitmasks, dp

## Description

You are given $n$ arrays $a_1$, $a_2$, ..., $a_n$; each array consists of exactly $m$ integers. We denote the $y$-th element of the $x$-th array as $a_{x, y}$.

You have to choose two arrays $a_i$ and $a_j$ ($1 \le i, j \le n$, it is possible that $i = j$). After that, you will obtain a new array $b$ consisting of $m$ integers, such that for every $k \in [1, m]$ $b_k = \max(a_{i, k}, a_{j, k})$.

Your goal is to choose $i$ and $j$ so that the value of $\min \limits_{k = 1}^{m} b_k$ is maximum possible.

## Input

The first line contains two integers $n$ and $m$ ($1 \le n \le 3 \cdot 10^5$, $1 \le m \le 8$) — the number of arrays and the number of elements in each array, respectively.

Then $n$ lines follow, the $x$-th line contains the array $a_x$ represented by $m$ integers $a_{x, 1}$, $a_{x, 2}$, ..., $a_{x, m}$ ($0 \le a_{x, y} \le 10^9$).

## Output

Print two integers $i$ and $j$ ($1 \le i, j \le n$, it is possible that $i = j$) — the indices of the two arrays you have to choose so that the value of $\min \limits_{k = 1}^{m} b_k$ is maximum possible. If there are multiple answers, print any of them.

## Examples

*Example 1 — input:*
```
6 5
5 0 3 1 2
1 8 9 1 3
1 2 3 4 5
9 1 0 3 7
2 3 0 6 3
6 4 1 7 0
```

*Example 1 — output:*
```
1 5
```
