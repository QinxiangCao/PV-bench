# 1787/B — Number Factorization

*Rating:* 1100 · *Limits:* 1.0s, 256.0 MB · *Tags:* greedy, math, number theory

## Description

Given an integer $n$.

Consider all pairs of integer arrays $a$ and $p$ of the same length such that $n = \prod a_i^{p_i}$ (i.e. $a_1^{p_1}\cdot a_2^{p_2}\cdot\ldots$) ($a_i>1; p_i>0$) and $a_i$ is the product of some (possibly one) distinct prime numbers.

For example, for $n = 28 = 2^2\cdot 7^1 = 4^1 \cdot 7^1$ the array pair $a = [2, 7]$, $p = [2, 1]$ is correct, but the pair of arrays $a = [4, 7]$, $p = [1, 1]$ is not, because $4=2^2$ is a product of non-distinct prime numbers.

Your task is to find the maximum value of $\sum a_i \cdot p_i$ (i.e. $a_1\cdot p_1 + a_2\cdot p_2 + \ldots$) over all possible pairs of arrays $a$ and $p$. Note that you do not need to minimize or maximize the length of the arrays.

## Input

Each test contains multiple test cases. The first line contains an integer $t$ ($1 \le t \le 1000$) — the number of test cases.

Each test case contains only one integer $n$ ($2 \le n \le 10^9$).

## Output

For each test case, print the maximum value of $\sum a_i \cdot p_i$.

## Note

In the first test case, $100 = 10^2$ so that $a = [10]$, $p = [2]$ when $\sum a_i \cdot p_i$ hits the maximum value $10\cdot 2 = 20$. Also, $a = [100]$, $p = [1]$ does not work since $100$ is not made of distinct prime factors.

In the second test case, we can consider $10$ as $10^1$, so $a = [10]$, $p = [1]$. Notice that when $10 = 2^1\cdot 5^1$, $\sum a_i \cdot p_i = 7$.

## Examples

*Example 1 — input:*
```
7
100
10
864
130056192
1000000000
2
999999018
```
*Example 1 — output:*
```
20
10
22
118
90
2
333333009
```
