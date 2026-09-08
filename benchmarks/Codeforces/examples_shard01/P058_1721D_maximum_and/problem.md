# 1721/D — Maximum AND

*Rating:* 1800 · *Limits:* 3.0s, 256.0 MB · *Tags:* bitmasks, dfs and similar, divide and conquer, greedy, sortings

## Description

You are given two arrays $a$ and $b$, consisting of $n$ integers each.

Let's define a function $f(a, b)$ as follows:

- let's define an array $c$ of size $n$, where $c_i = a_i \oplus b_i$ ($\oplus$ denotes bitwise XOR);
- the value of the function is $c_1 \mathbin{\&} c_2 \mathbin{\&} \cdots \mathbin{\&} c_n$ (i.e. bitwise AND of the entire array $c$).

Find the maximum value of the function $f(a, b)$ if you can reorder the array $b$ in an arbitrary way (leaving the initial order is also an option).

## Input

The first line contains one integer $t$ ($1 \le t \le 10^4$) — the number of test cases.

The first line of each test case contains one integer $n$ ($1 \le n \le 10^5$) — the size of arrays $a$ and $b$.

The second line contains $n$ integers $a_1, a_2, \dots, a_n$ ($0 \le a_i < 2^{30}$).

The third line contains $n$ integers $b_1, b_2, \dots, b_n$ ($0 \le b_i < 2^{30}$).

The sum of $n$ over all test cases does not exceed $10^5$.

## Output

For each test case print one integer — the maximum value of the function $f(a, b)$ if you can reorder the array $b$ in an arbitrary way.

## Examples

*Example 1 — input:*
```
3
5
1 0 0 3 3
2 3 2 1 0
3
1 1 1
0 0 3
8
0 1 2 3 4 5 6 7
7 6 5 4 3 2 1 0
```

*Example 1 — output:*
```
2
0
7
```
