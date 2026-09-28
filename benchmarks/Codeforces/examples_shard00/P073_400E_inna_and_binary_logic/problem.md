# 400/E — Inna and Binary Logic

*Rating:* 2100 · *Limits:* 3.0s, 256.0 MB · *Tags:* binary search, bitmasks, data structures

## Description

Inna is fed up with jokes about female logic. So she started using binary logic instead.

Inna has an array of n elements a1[1], a1[2], ..., a1[n]. Girl likes to train in her binary logic, so she does an exercise consisting of n stages: on the first stage Inna writes out all numbers from array a1, on the i-th (i ≥ 2) stage girl writes all elements of array ai, which consists of n - i + 1 integers; the k-th integer of array ai is defined as follows: ai[k] = ai - 1[k] AND ai - 1[k + 1]. Here AND is bit-wise binary logical operation.

Dima decided to check Inna's skill. He asks Inna to change array, perform the exercise and say the sum of all $$\frac{n(n+1)}{2}$$ elements she wrote out during the current exercise.

Help Inna to answer the questions!

## Input

The first line contains two integers n and m (1 ≤ n, m ≤ 105) — size of array a1 and number of Dima's questions. Next line contains n integers a1[1], a1[2], ..., a1[n] (0 ≤ ai ≤ 105) — initial array elements.

Each of next m lines contains two integers — Dima's question description. Each question consists of two integers pi, vi (1 ≤ pi ≤ n; 0 ≤ vi ≤ 105). For this question Inna should make a1[pi] equals vi, and then perform the exercise. Please, note that changes are saved from question to question.

## Output

For each question print Inna's answer on a single line.

## Examples

*Example 1 — input:*
```
3 4
1 1 1
1 1
2 2
3 2
1 2
```

*Example 1 — output:*
```
6
4
7
12
```
