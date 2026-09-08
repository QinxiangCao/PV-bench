# P3865 — Sparse Table and Range Maximum Query

## Description

Given a sequence of length $N$ and $M$ queries, find the maximum value in the
specified interval for every query. Each query must be answered in $O(1)$
time after preprocessing.

## Input

The first line contains two integers $N$ and $M$, representing the length of
the sequence and the number of queries.

The second line contains $N$ integers $a_1,\ldots,a_N$.

Each of the next $M$ lines contains two integers $l_i$ and $r_i$, representing
the inclusive query interval $[l_i,r_i]$.

## Output

Print $M$ lines. The $i$-th line contains the maximum value in the interval
$[l_i,r_i]$.

## Constraints

- $1 \le N \le 10^5$.
- $1 \le M \le 2\times10^6$.
- $0 \le a_i \le 10^9$.
- $1 \le l_i \le r_i \le N$.

## Source

[Luogu P3865, "Sparse Table and RMQ"](https://www.luogu.com.cn/problem/P3865?lang=en).
