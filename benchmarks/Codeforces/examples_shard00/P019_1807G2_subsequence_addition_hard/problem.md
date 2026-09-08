# 1807/G2 — Subsequence Addition (Hard Version)

*Rating:* 1100 · *Limits:* 2.0s, 256.0 MB · *Tags:* bitmasks, dp, greedy, implementation, sortings

## Description

The only difference between the two versions is that in this version, the constraints are higher.

Initially, array $a$ contains just the number $1$. You can perform several operations in order to change the array. In an operation, you can select some subsequence$^{\dagger}$ of $a$ and add into $a$ an element equal to the sum of all elements of the subsequence.

You are given a final array $c$. Check if $c$ can be obtained from the initial array $a$ by performing some number (possibly 0) of operations on the initial array.

$^{\dagger}$ A sequence $b$ is a subsequence of a sequence $a$ if $b$ can be obtained from $a$ by the deletion of several (possibly zero, but not all) elements. In other words, select $k$ ($1 \leq k \leq |a|$) distinct indices $i_1, i_2, \dots, i_k$ and insert anywhere into $a$ a new element with the value equal to $a_{i_1} + a_{i_2} + \dots + a_{i_k}$.

## Input

The first line of the input contains an integer $t$ ($1 \leq t \leq 1000$) — the number of test cases. The description of the test cases follows.

The first line of each test case contains a single integer $n$ ($1 \leq n \leq 2 \cdot 10^5$)  — the number of elements the final array $c$ should have.

The second line of each test case contains $n$ space-separated integers $c_i$ ($1 \leq c_i \leq 2 \cdot 10^5$)  — the elements of the final array $c$ that should be obtained from the initial array $a$.

It is guaranteed that the sum of $n$ over all test cases does not exceed $2 \cdot 10^5$.

## Output

For each test case, output "YES" (without quotes) if such a sequence of operations exists, and "NO" (without quotes) otherwise.

You can output the answer in any case (for example, the strings "yEs", "yes", "Yes" and "YES" will be recognized as a positive answer).

## Note

For the first test case, the initial array $a$ is already equal to $[1]$, so the answer is "YES".

For the second test case, performing any amount of operations will change $a$ to an array of size at least two which doesn't only have the element $2$, thus obtaining the array $[2]$ is impossible and the answer is "NO".

For the third test case, we can perform the following operations in order to obtain the final given array $c$:

- Initially, $a = [1]$.
- By choosing the subsequence $[1]$, and inserting $1$ in the array, $a$ changes to $[1, 1]$.
- By choosing the subsequence $[1, 1]$, and inserting $1+1=2$ in the middle of the array, $a$ changes to $[1, 2, 1]$.
- By choosing the subsequence $[1, 2]$, and inserting $1+2=3$ after the first $1$ of the array, $a$ changes to $[1, 3, 2, 1]$.
- By choosing the subsequence $[1, 3, 1]$ and inserting $1+3+1=5$ at the beginning of the array, $a$ changes to $[5, 1, 3, 2, 1]$ (which is the array we needed to obtain).

## Examples

*Example 1 — input:*
```
6
1
1
1
2
5
5 1 3 2 1
5
7 1 5 2 1
3
1 1 1
5
1 1 4 2 1
```

*Example 1 — output:*
```
YES
NO
YES
NO
YES
YES
```
