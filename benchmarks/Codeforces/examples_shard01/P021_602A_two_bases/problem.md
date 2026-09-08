# 602/A — Two Bases

*Rating:* 1100 · *Limits:* 1.0s, 256.0 MB · *Tags:* brute force, implementation

## Description

After seeing the "ALL YOUR BASE ARE BELONG TO US" meme for the first time, numbers $X$ and $Y$ realised that they have different bases, which complicated their relations.

You're given a number $X$ represented in base $bx$ and a number $Y$ represented in base $by$. Compare those two numbers.

## Input

The first line of the input contains two space-separated integers $n$ and $bx$ ($1 \le n \le 10$, $2 \le bx \le 40$), where $n$ is the number of digits in the $bx$-based representation of $X$.

The second line contains $n$ space-separated integers $x_1, x_2, \ldots, x_n$ ($0 \le x_i < bx$) — the digits of $X$. They are given in the order from the most significant digit to the least significant one.

The following two lines describe $Y$ in the same way: the third line contains two space-separated integers $m$ and $by$ ($1 \le m \le 10$, $2 \le by \le 40$, $bx \ne by$), where $m$ is the number of digits in the $by$-based representation of $Y$, and the fourth line contains $m$ space-separated integers $y_1, y_2, \ldots, y_m$ ($0 \le y_i < by$) — the digits of $Y$.

There will be no leading zeroes. Both $X$ and $Y$ will be positive. All digits of both numbers are given in the standard decimal numeral system.

## Output

Output a single character (quotes for clarity):

- '<' if $X < Y$
- '>' if $X > Y$
- '=' if $X = Y$

## Note

In the first sample, $X = 101111_2 = 47_{10} = Y$.

In the second sample, $X = 102_3 = 21_5$ and $Y = 24_5 = 112_3$, thus $X < Y$.

In the third sample, $X = \text{FF4007A}_{16}$ and $Y = 4803150_9$. We may notice that $X$ starts with much larger digits and $bx$ is much larger than $by$, so $X$ is clearly larger than $Y$.

## Examples

*Example 1 — input:*
```
6 2
1 0 1 1 1 1
2 10
4 7
```
*Example 1 — output:*
```
=
```

*Example 2 — input:*
```
3 3
1 0 2
2 5
2 4
```
*Example 2 — output:*
```
<
```

*Example 3 — input:*
```
7 16
15 15 4 0 0 7 10
7 9
4 8 0 3 1 5 0
```
*Example 3 — output:*
```
>
```
