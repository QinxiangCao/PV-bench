# P1368 Minimal Representation

## Description

Given a circular sequence of $n$ integers, output its lexicographically
smallest cyclic rotation.

The verification function `minimal_representation` receives the sequence, a
working buffer, and an output array. It writes the smallest rotation into the
output array and returns the corresponding zero-based starting position in the
input sequence.

## Input

The first line contains $n$ and the second line contains the cyclic sequence.

## Output

Print the lexicographically smallest rotation of the sequence.

## Constraints

- Original problem: $1 \le n \le 300000$.
- Verification case: $1 \le n \le 1000$.
- Every sequence value is a signed C `int`.

## Source

[Luogu P1368, "Minimal Representation"](https://www.luogu.com.cn/problem/P1368).
