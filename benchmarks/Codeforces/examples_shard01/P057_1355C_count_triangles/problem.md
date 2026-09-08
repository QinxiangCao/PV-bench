# 1355/C — Count Triangles

*Rating:* 1800 · *Limits:* 1.0s, 256.0 MB · *Tags:* binary search, implementation, math, two pointers

## Description

Like any unknown mathematician, Yuri has favourite numbers: $A$, $B$, $C$, and $D$, where $A \leq B \leq C \leq D$. Yuri also likes triangles and once he thought: how many non-degenerate triangles with integer sides $x$, $y$, and $z$ exist, such that $A \leq x \leq B \leq y \leq C \leq z \leq D$ holds?

Yuri is preparing problems for a new contest now, so he is very busy. That's why he asked you to calculate the number of triangles with described property.

The triangle is called non-degenerate if and only if its vertices are not collinear.

## Input

The first line contains four integers: $A$, $B$, $C$ and $D$ ($1 \leq A \leq B \leq C \leq D \leq 5 \cdot 10^5$) — Yuri's favourite numbers.

## Output

Print the number of non-degenerate triangles with integer sides $x$, $y$, and $z$ such that the inequality $A \leq x \leq B \leq y \leq C \leq z \leq D$ holds.

## Note

In the first example Yuri can make up triangles with sides $(1, 3, 3)$, $(2, 2, 3)$, $(2, 3, 3)$ and $(2, 3, 4)$.

In the second example Yuri can make up triangles with sides $(1, 2, 2)$, $(2, 2, 2)$ and $(2, 2, 3)$.

In the third example Yuri can make up only one equilateral triangle with sides equal to $5 \cdot 10^5$.

## Examples

*Example 1 — input:*
```
1 2 3 4
```

*Example 1 — output:*
```
4
```

*Example 2 — input:*
```
1 2 2 5
```

*Example 2 — output:*
```
3
```

*Example 3 — input:*
```
500000 500000 500000 500000
```

*Example 3 — output:*
```
1
```
