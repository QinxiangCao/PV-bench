# 1492/D — Genius's Gambit

*Rating:* 1900 · *Limits:* 2.0s, 512.0 MB · *Tags:* bitmasks, constructive algorithms, greedy, math

## Description

You are given three integers $a$, $b$, $k$.

Find two binary integers $x$ and $y$ ($x \ge y$) such that

1. both $x$ and $y$ consist of $a$ zeroes and $b$ ones;
2. $x - y$ (also written in binary form) has exactly $k$ ones.

## Input

The only line contains three integers $a$, $b$, and $k$ ($0 \leq a$; $1 \leq b$; $0 \leq k \leq a + b \leq 2 \cdot 10^5$) — the number of zeroes, ones, and the number of ones in the result.

## Output

If it's possible to find two suitable integers, print "Yes" followed by $x$ and $y$ in base-2.

Otherwise print "No".

If there are multiple possible answers, print any of them.

## Note

In the first example, $x = 101000_2 = 2^5 + 2^3 = 40_{10}$, $y = 100001_2 = 2^5 + 2^0 = 33_{10}$, $40_{10} - 33_{10} = 7_{10} = 2^2 + 2^1 + 2^0 = 111_{2}$. Hence $x-y$ has $3$ ones in base-2.

In the second example, $x = 10100_2 = 2^4 + 2^2 = 20_{10}$, $y = 10010_2 = 2^4 + 2^1 = 18$, $x - y = 20 - 18 = 2_{10} = 10_{2}$. This is precisely one 1.

In the third example, one may show, that it's impossible to find an answer.

## Examples

*Example 1 — input:*
```
4 2 3
```

*Example 1 — output:*
```
Yes
101000
100001
```

*Example 2 — input:*
```
3 2 1
```

*Example 2 — output:*
```
Yes
10100
10010
```

*Example 3 — input:*
```
3 2 5
```

*Example 3 — output:*
```
No
```
