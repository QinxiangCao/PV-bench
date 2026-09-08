# 459/A — Pashmak and Garden

*Rating:* 1200 · *Limits:* 1.0s, 256.0 MB · *Tags:* implementation

## Description

Pashmak has fallen in love with an attractive girl called Parmida since one year ago...

Today, Pashmak set up a meeting with his partner in a romantic garden. Unfortunately, Pashmak has forgotten where the garden is. But he remembers that the garden looks like a square with sides parallel to the coordinate axes. He also remembers that there is exactly one tree on each vertex of the square. Now, Pashmak knows the position of only two of the trees. Help him to find the position of two remaining ones.

## Input

The first line contains four space-separated $x_1$, $y_1$, $x_2$, $y_2$ ($-100 \le x_1, y_1, x_2, y_2 \le 100$) integers, where $x_1$ and $y_1$ are coordinates of the first tree and $x_2$ and $y_2$ are coordinates of the second tree. It's guaranteed that the given points are distinct.

## Output

If there is no solution to the problem, print -1. Otherwise print four space-separated integers $x_3$, $y_3$, $x_4$, $y_4$ that correspond to the coordinates of the two other trees. If there are several solutions you can output any of them.

Note that $x_3$, $y_3$, $x_4$, $y_4$ must be in the range ($-1000 \le x_3, y_3, x_4, y_4 \le 1000$).

## Examples

*Example 1 — input:*
```
0 0 0 1
```
*Example 1 — output:*
```
1 0 1 1
```

*Example 2 — input:*
```
0 0 1 1
```
*Example 2 — output:*
```
0 1 1 0
```

*Example 3 — input:*
```
0 0 1 2
```
*Example 3 — output:*
```
-1
```
