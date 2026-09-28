# 1967/B2 — Reverse Card (Hard Version)

*Rating:* 2200 · *Limits:* 2.0s, 256.0 MB · *Tags:* brute force, math, number theory

## Description

The two versions are different problems. You may want to read both versions. You can make hacks only if both versions are solved.

You are given two positive integers $n$, $m$.

Calculate the number of ordered pairs $(a, b)$ satisfying the following conditions:

- $1\le a\le n$, $1\le b\le m$;
- $b \cdot \gcd(a,b)$ is a multiple of $a+b$.

## Input

Each test contains multiple test cases. The first line contains the number of test cases $t$ ($1\le t\le 10^4$). The description of the test cases follows.

The first line of each test case contains two integers $n$, $m$ ($1\le n,m\le 2 \cdot 10^6$).

It is guaranteed that neither the sum of $n$ nor the sum of $m$ over all test cases exceeds $2 \cdot 10^6$.

## Output

For each test case, print a single integer: the number of valid pairs.

## Note

In the first test case, no pair satisfies the conditions.

In the fourth test case, $(2,2),(3,6),(4,4),(6,3),(6,6),(8,8)$ satisfy the conditions.

## Examples

*Example 1 — input:*
```
6
1 1
2 3
3 5
10 8
100 1233
1000000 1145141
```

*Example 1 — output:*
```
0
1
1
6
423
5933961
```
