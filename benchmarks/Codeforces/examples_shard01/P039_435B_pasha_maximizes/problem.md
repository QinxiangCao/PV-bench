# 435/B — Pasha Maximizes

*Rating:* 1400 · *Limits:* 1.0s, 256.0 MB · *Tags:* greedy

## Description

Pasha has a positive integer $a$ without leading zeroes. Today he decided that the number is too small and he should make it larger. Unfortunately, the only operation Pasha can do is to swap two adjacent decimal digits of the integer.

Help Pasha count the maximum number he can get if he has the time to make at most $k$ swaps.

## Input

The single line contains two integers $a$ and $k$ ($1 \le a \le 10^{18}$; $0 \le k \le 100$).

## Output

Print the maximum number that Pasha can get if he makes at most $k$ swaps.

## Examples

*Example 1 — input:*
```
1990 1
```
*Example 1 — output:*
```
9190
```

*Example 2 — input:*
```
300 0
```
*Example 2 — output:*
```
300
```

*Example 3 — input:*
```
1034 2
```
*Example 3 — output:*
```
3104
```

*Example 4 — input:*
```
9090000078001234 6
```
*Example 4 — output:*
```
9907000008001234
```
