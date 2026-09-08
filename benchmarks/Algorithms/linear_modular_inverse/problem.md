# P3811 — Multiplicative Inverses Modulo a Prime

## Description

Given positive integers $n$ and $p$, find the multiplicative inverse modulo
$p$ of every integer in $[1,n]$.

An integer $x$ is a multiplicative inverse of $a$ modulo $p$ if

$$
ax \equiv 1 \pmod p.
$$

The input guarantees that $p$ is prime.

## Input

The only line contains two positive integers $n$ and $p$.

## Output

Print $n$ lines. The $i$-th line contains the multiplicative inverse of $i$
modulo $p$.

## Constraints

- $1 \le n \le 3\times10^6$.
- $n < p < 20000528$.
- $p$ is prime.

## Source

[Luogu P3811, "Multiplicative Inverses Modulo a Prime"](https://www.luogu.com.cn/problem/P3811).
