# 460/A — Vasya and Socks

*Rating:* 900 · *Limits:* 1.0s, 256.0 MB · *Tags:* brute force, implementation, math

## Description

Vasya has n pairs of socks. In the morning of each day Vasya has to put on a pair of socks before he goes to school. When he comes home in the evening, Vasya takes off the used socks and throws them away. Every m-th day (at days with numbers m, 2m, 3m, ...) mom buys a pair of socks to Vasya. She does it late in the evening, so that Vasya cannot put on a new pair of socks before the next day. How many consecutive days pass until Vasya runs out of socks?

## Input

The single line contains two integers n and m (1 ≤ n ≤ 100; 2 ≤ m ≤ 100), separated by a space.

## Output

Print a single integer — the answer to the problem.

## Note

In the first sample Vasya spends the first two days wearing the socks that he had initially. Then on day three he puts on the socks that were bought on day two.

In the second sample Vasya spends the first nine days wearing the socks that he had initially. Then he spends three days wearing the socks that were bought on the third, sixth and ninth days. Than he spends another day wearing the socks that were bought on the twelfth day.

## Examples

*Example 1 — input:*
```
2 2
```
*Example 1 — output:*
```
3
```

*Example 2 — input:*
```
9 3
```
*Example 2 — output:*
```
13
```
