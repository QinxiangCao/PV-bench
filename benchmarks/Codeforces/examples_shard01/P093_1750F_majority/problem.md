# 1750/F — Majority

*Rating:* 2700 · *Limits:* 2.0s, 1024.0 MB · *Tags:* combinatorics, dp, math, strings

## Description

Everyone was happy coding, until suddenly a power shortage happened and the best competitive programming site went down. Fortunately, a system administrator bought some new equipment recently, including some UPSs. Thus there are some servers that are still online, but we need all of them to be working in order to keep the round rated.

Imagine the servers being a binary string $s$ of length $n$. If the $i$-th server is online, then $s_i = 1$, and $s_i = 0$ otherwise.

A system administrator can do the following operation called electricity spread, that consists of the following phases:

- Select two servers at positions $1 \le i < j \le n$ such that both are online (i.e. $s_i=s_j=1$). The spread starts only from online servers.
- Check if we have enough power to make the spread. We consider having enough power if the number of turned on servers in range $[i, j]$ is at least the number of turned off servers in range $[i, j]$. More formally, check whether $2 \cdot (s_i + s_{i+1} + \ldots + s_j) \ge j - i + 1$.
- If the check is positive, turn on all the offline servers in range $[i, j]$. More formally, make $s_k := 1$ for all $k$ from $i$ to $j$.

We call a binary string $s$ of length $n$ rated if we can turn on all servers (i.e. make $s_i = 1$ for $1 \le i \le n$) using the electricity spread operation any number of times (possibly, $0$). Your task is to find the number of rated strings of length $n$ modulo $m$.

## Input

The first and only line contains two integers $n$ and $m$ ($1 \le n \le 5000$, $10 \le m \le 10^9$) — the length of the string and the required module.

## Output

Print a single integer — the number of rated binary strings of length $n$. Since this number can be large, print it modulo $m$.

## Note

In the first example, the only rated string is 11. So the answer is $1$.

In the second example, the rated strings are:

- 111;
- 101, because we can perform an operation with $i = 1$ and $j = 3$.

In the third sample, the rated strings are:

- 1001;
- 1111;
- 1011;
- 1101.

## Examples

*Example 1 — input:*
```
2 100
```

*Example 1 — output:*
```
1
```

*Example 2 — input:*
```
3 10
```

*Example 2 — output:*
```
2
```

*Example 3 — input:*
```
4 3271890
```

*Example 3 — output:*
```
4
```

*Example 4 — input:*
```
17 123456
```

*Example 4 — output:*
```
32347
```
