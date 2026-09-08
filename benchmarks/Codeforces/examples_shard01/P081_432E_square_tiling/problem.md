# 432/E — Square Tiling

*Rating:* 2300 · *Limits:* 1.0s, 256.0 MB · *Tags:* constructive algorithms, greedy

## Description

You have an n × m rectangle table, its cells are not initially painted. Your task is to paint all cells of the table. The resulting picture should be a tiling of the table with squares. More formally:

- each cell must be painted some color (the colors are marked by uppercase Latin letters);
- we will assume that two cells of the table are connected if they are of the same color and share a side; each connected region of the table must form a square.

Given n and m, find lexicographically minimum coloring of the table that meets the described properties.

## Input

The first line contains two integers, n and m (1 ≤ n, m ≤ 100).

## Output

Print lexicographically minimum coloring of the table that meets the described conditions.

One coloring (let's call it X) is considered lexicographically less than the other one (let's call it Y), if:

- consider all the table cells from left to right and from top to bottom (first, the first cell in the first row, then the second cell in the first row and so on);
- let's find in this order the first cell that has distinct colors in two colorings;
- the letter that marks the color of the cell in X, goes alphabetically before the letter that marks the color of the cell in Y.

## Examples

*Example 1 — input:*
```
1 3
```

*Example 1 — output:*
```
ABA
```

*Example 2 — input:*
```
2 2
```

*Example 2 — output:*
```
AA
AA
```

*Example 3 — input:*
```
3 4
```

*Example 3 — output:*
```
AAAB
AAAC
AAAB
```
