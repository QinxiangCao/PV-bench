# P4999 — Annoying Math Homework

## Description

For a nonnegative integer $x$, let $s(x)$ be the sum of its decimal digits.
For every query containing two integers $L$ and $R$, compute

$$
\left(\sum_{x=L}^{R}s(x)\right) \bmod (10^9+7).
$$

## Input

The first line contains one integer $T$, the number of queries.

Each of the next $T$ lines contains two integers $L$ and $R$.

## Output

For each query, print one line containing the sum of the decimal-digit sums of
all integers in $[L,R]$, modulo $10^9+7$.

## Constraints

- $1 \le T \le 20$.
- $1 \le L \le R \le 10^{18}$.
- For 50% of the test data, $R \le 10^8$.

## Source

[Luogu P4999, "Annoying Math Homework"](https://www.luogu.com.cn/problem/P4999?lang=en).
