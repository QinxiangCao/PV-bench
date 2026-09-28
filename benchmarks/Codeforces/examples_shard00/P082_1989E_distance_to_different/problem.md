# 1989/E — Distance to Different

*Rating:* 2300 · *Limits:* 2.0s, 512.0 MB · *Tags:* combinatorics, dp, math

## Description

Consider an array $a$ of $n$ integers, where every element is from $1$ to $k$, and every integer from $1$ to $k$ appears at least once.

Let the array $b$ be constructed as follows: for the $i$-th element of $a$, $b_i$ is the distance to the closest element in $a$ which is not equal to $a_i$. In other words, $b_i = \min \limits_{j \in [1, n], a_j \ne a_i} |i - j|$.

For example, if $a = [1, 1, 2, 3, 3, 3, 3, 1]$, then $b = [2, 1, 1, 1, 2, 2, 1, 1]$.

Calculate the number of different arrays $b$ you can obtain if you consider all possible arrays $a$, and print it modulo $998244353$.

## Input

The only line of the input contains two integers $n$ and $k$ ($2 \le n \le 2 \cdot 10^5$; $2 \le k \le \min(n, 10)$).

## Output

Print one integer — the number of different arrays $b$ you can obtain, taken modulo $998244353$.

## Examples

*Example 1 — input:*
```
2 2
```

*Example 1 — output:*
```
1
```

*Example 2 — input:*
```
4 3
```

*Example 2 — output:*
```
3
```

*Example 3 — input:*
```
6 2
```

*Example 3 — output:*
```
20
```

*Example 4 — input:*
```
6 5
```

*Example 4 — output:*
```
3
```

*Example 5 — input:*
```
133 7
```

*Example 5 — output:*
```
336975971
```
