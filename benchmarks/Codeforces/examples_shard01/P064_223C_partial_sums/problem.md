# 223/C — Partial Sums

*Rating:* 1900 · *Limits:* 4.0s, 256.0 MB · *Tags:* combinatorics, math, number theory

## Description

You've got an array a, consisting of n integers. The array elements are indexed from 1 to n. Let's determine a two step operation like that:

1. First we build by the array a an array s of partial sums, consisting of n elements. Element number i (1 ≤ i ≤ n) of array s equals $$s_i = \left( \sum_{j=1}^{i} a_j \right) \mod (10^9 + 7)$$. The operation x mod y means that we take the remainder of the division of number x by number y.
2. Then we write the contents of the array s to the array a. Element number i (1 ≤ i ≤ n) of the array s becomes the i-th element of the array a (ai = si).

You task is to find array a after exactly k described operations are applied.

## Input

The first line contains two space-separated integers n and k (1 ≤ n ≤ 2000, 0 ≤ k ≤ 109). The next line contains n space-separated integers a1, a2, ..., an — elements of the array a (0 ≤ ai ≤ 109).

## Output

Print n integers  — elements of the array a after the operations are applied to it. Print the elements in the order of increasing of their indexes in the array a. Separate the printed numbers by spaces.

## Examples

*Example 1 — input:*
```
3 1
1 2 3
```

*Example 1 — output:*
```
1 3 6
```

*Example 2 — input:*
```
5 0
3 14 15 92 6
```

*Example 2 — output:*
```
3 14 15 92 6
```
