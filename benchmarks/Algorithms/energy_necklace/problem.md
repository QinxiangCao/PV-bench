# P1063 Energy Necklace

## Description

Each bead has a head and tail label, and adjacent labels match. Merging beads
$(m,r)$ and $(r,n)$ releases $m r n$ energy and creates bead $(m,n)$. Repeatedly
merge adjacent beads until one remains. Choose the merge order that maximizes
total released energy.

## Input

The first line contains $N$. The second line contains the $N$ head labels in clockwise order.

## Output

Print the maximum total energy.

## Constraints

- $4 \le N \le 100$.
- Every label is a positive integer not exceeding $1000$.
- The answer does not exceed $2.1\times10^9$.

## Source

[Luogu P1063, NOIP 2006 Senior](https://www.luogu.com.cn/problem/P1063).
