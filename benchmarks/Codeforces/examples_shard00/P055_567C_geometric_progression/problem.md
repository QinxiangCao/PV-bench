# 567/C — Geometric Progression

*Rating:* 1700 · *Limits:* 1.0s, 256.0 MB · *Tags:* binary search, data structures, dp

## Description

Polycarp loves geometric progressions very much. Since he was only three years old, he loves only the progressions of length three. He also has a favorite integer k and a sequence a, consisting of n integers.

He wants to know how many subsequences of length three can be selected from a, so that they form a geometric progression with common ratio k.

A subsequence of length three is a combination of three such indexes i1, i2, i3, that 1 ≤ i1 < i2 < i3 ≤ n. That is, a subsequence of length three are such groups of three elements that are not necessarily consecutive in the sequence, but their indexes are strictly increasing.

A geometric progression with common ratio k is a sequence of numbers of the form b·k0, b·k1, ..., b·kr - 1.

Polycarp is only three years old, so he can not calculate this number himself. Help him to do it.

## Input

The first line of the input contains two integers, n and k (1 ≤ n, k ≤ 2·105), showing how many numbers Polycarp's sequence has and his favorite number.

The second line contains n integers a1, a2, ..., an ( - 109 ≤ ai ≤ 109) — elements of the sequence.

## Output

Output a single number — the number of ways to choose a subsequence of length three, such that it forms a geometric progression with a common ratio k.

## Note

In the first sample test the answer is four, as any of the two 1s can be chosen as the first element, the second element can be any of the 2s, and the third element of the subsequence must be equal to 4.

## Examples

*Example 1 — input:*
```
5 2
1 1 2 2 4
```

*Example 1 — output:*
```
4
```

*Example 2 — input:*
```
3 1
1 1 1
```

*Example 2 — output:*
```
1
```

*Example 3 — input:*
```
10 3
1 2 6 2 3 6 9 18 3 9
```

*Example 3 — output:*
```
6
```
