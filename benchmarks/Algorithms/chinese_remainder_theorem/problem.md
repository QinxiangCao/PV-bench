# P1495 — Chinese Remainder Theorem / Cao Chong Raises Pigs

## Description

Given $n$ congruences

$$
x \equiv b_i \pmod {a_i},
$$

where $a_1,\ldots,a_n$ are pairwise coprime, find the smallest nonnegative
integer $x$ satisfying all the congruences.

## Input

The first line contains one integer $n$, the number of congruences.

Each of the next $n$ lines contains two integers $a_i$ and $b_i$, meaning that
dividing $x$ by $a_i$ leaves remainder $b_i$.

## Output

Print one nonnegative integer: the smallest value of $x$ satisfying all the
congruences.

## Constraints

- $1 \le n \le 10$.
- $0 \le b_i < a_i \le 100000$.
- The values $a_1,\ldots,a_n$ are pairwise coprime.
- $1 \le \prod_{i=1}^{n} a_i \le 10^{18}$.

## Source

[Luogu P1495, "Chinese Remainder Theorem / Cao Chong Raises Pigs"](https://www.luogu.com.cn/problem/P1495).
