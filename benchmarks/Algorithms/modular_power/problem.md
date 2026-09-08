# P1226 — Fast Modular Exponentiation

## Description

Given three integers $a$, $b$, and $p$, compute

$$
a^b \bmod p.
$$

## Input

The only line contains three integers $a$, $b$, and $p$.

## Output

Print one line in the following format:

```text
a^b mod p=s
```

Here `a`, `b`, and `p` are the input values, and $s=a^b\bmod p$.

## Constraints

- $0 \le a,b < 2^{31}$.
- $a+b>0$.
- $2 \le p < 2^{31}$.

## Source

[Luogu P1226, "Fast Modular Exponentiation"](https://www.luogu.com.cn/problem/P1226).
