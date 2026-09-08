# LeetCode 11: Container With Most Water

## Description

An array `height` describes vertical lines at integer x-coordinates: line $i$
extends from $(i,0)$ to $(i,height_i)$. Choose two lines which, together with
the x-axis, form a non-slanted container holding as much water as possible,
and return that maximum amount.

## Input

The function receives an integer array `height` and four writable work arrays.

## Output

Return the maximum amount of water that can be contained by two lines.

## Constraints

- $n = \operatorname{length}(height)$.
- $2 \le n \le 10^5$.
- $0 \le height_i \le 10^4$.

Under these bounds the maximum possible area is
$(10^5-1)\times10^4=999{,}990{,}000$, which fits in a 32-bit signed integer.

## Source

[LeetCode 11, "Container With Most Water"](https://leetcode.com/problems/container-with-most-water/).
