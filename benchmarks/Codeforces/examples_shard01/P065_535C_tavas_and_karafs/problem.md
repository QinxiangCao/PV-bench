# 535/C — Tavas and Karafs

*Rating:* 1900 · *Limits:* 2.0s, 256.0 MB · *Tags:* binary search, greedy, math

## Description

Karafs is some kind of vegetable in shape of an 1 × h rectangle. Tavaspolis people love Karafs and they use Karafs in almost any kind of food. Tavas, himself, is crazy about Karafs.

Each Karafs has a positive integer height. Tavas has an infinite 1-based sequence of Karafses. The height of the i-th Karafs is si = A + (i - 1) × B.

For a given m, let's define an m-bite operation as decreasing the height of at most m distinct not eaten Karafses by 1. Karafs is considered as eaten when its height becomes zero.

Now SaDDas asks you n queries. In each query he gives you numbers l, t and m and you should find the largest number r such that l ≤ r and sequence sl, sl + 1, ..., sr can be eaten by performing m-bite no more than t times or print -1 if there is no such number r.

## Input

The first line of input contains three integers A, B and n (1 ≤ A, B ≤ 106, 1 ≤ n ≤ 105).

Next n lines contain information about queries. i-th line contains integers l, t, m (1 ≤ l, t, m ≤ 106) for i-th query.

## Output

For each query, print its answer in a single line.

## Examples

*Example 1 — input:*
```
2 1 4
1 5 3
3 3 10
7 10 2
6 4 8
```

*Example 1 — output:*
```
4
-1
8
-1
```

*Example 2 — input:*
```
1 5 2
1 5 10
2 7 4
```

*Example 2 — output:*
```
1
2
```
