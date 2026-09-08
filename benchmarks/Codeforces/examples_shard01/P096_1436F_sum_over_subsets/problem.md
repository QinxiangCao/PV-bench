# 1436/F — Sum Over Subsets

*Rating:* 2800 · *Limits:* 1.0s, 256.0 MB · *Tags:* combinatorics, math, number theory

## Description

You are given a multiset $S$. Over all pairs of subsets $A$ and $B$, such that:

- $B \subset A$;
- $|B| = |A| - 1$;
- greatest common divisor of all elements in $A$ is equal to one;

find the sum of $\sum_{x \in A}{x} \cdot \sum_{x \in B}{x}$, modulo $998\,244\,353$.

## Input

The first line contains one integer $m$ ($1 \le m \le 10^5$): the number of different values in the multiset $S$.

Each of the next $m$ lines contains two integers $a_i$, $freq_i$ ($1 \le a_i \le 10^5, 1 \le freq_i \le 10^9$). Element $a_i$ appears in the multiset $S$ $freq_i$ times. All $a_i$ are different.

## Output

Print the required sum, modulo $998\,244\,353$.

## Note

A multiset is a set where elements are allowed to coincide. $|X|$ is the cardinality of a set $X$, the number of elements in it.

$A \subset B$: Set $A$ is a subset of a set $B$.

In the first example $B=\{1\}, A=\{1,2\}$ and $B=\{2\}, A=\{1, 2\}$ have a product equal to $1\cdot3 + 2\cdot3=9$. Other pairs of $A$ and $B$ don't satisfy the given constraints.

## Examples

*Example 1 — input:*
```
2
1 1
2 1
```

*Example 1 — output:*
```
9
```

*Example 2 — input:*
```
4
1 1
2 1
3 1
6 1
```

*Example 2 — output:*
```
1207
```

*Example 3 — input:*
```
1
1 5
```

*Example 3 — output:*
```
560
```
