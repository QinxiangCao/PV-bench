# 440/B — Balancer

*Rating:* 1600 · *Limits:* 0.5s, 256.0 MB · *Tags:* greedy, implementation

## Description

Petya has k matches, placed in n matchboxes lying in a line from left to right. We know that k is divisible by n. Petya wants all boxes to have the same number of matches inside. For that, he can move a match from its box to the adjacent one in one move. How many such moves does he need to achieve the desired configuration?

## Input

The first line contains integer n (1 ≤ n ≤ 50000). The second line contains n non-negative numbers that do not exceed 109, the i-th written number is the number of matches in the i-th matchbox. It is guaranteed that the total number of matches is divisible by n.

## Output

Print the total minimum number of moves.

## Examples

*Example 1 — input:*
```
6
1 6 2 5 3 7
```

*Example 1 — output:*
```
12
```
