# 1903/C — Theofanis' Nightmare

*Rating:* 1400 · *Limits:* 1.0s, 256.0 MB · *Tags:* constructive algorithms, greedy

## Description

Theofanis easily gets obsessed with problems before going to sleep and often has nightmares about them. To deal with his obsession he visited his doctor, Dr. Emix.

In his latest nightmare, he has an array $a$ of size $n$ and wants to divide it into non-empty subarrays$^{\dagger}$ such that every element is in exactly one of the subarrays.

For example, the array $[1,-3,7,-6,2,5]$ can be divided to $[1] [-3,7] [-6,2] [5]$.

The Cypriot value of such division is equal to $\Sigma_{i=1}^{k} i \cdot \mathrm{sum}_i$ where $k$ is the number of subarrays that we divided the array into and $\mathrm{sum}_i$ is the sum of the $i$-th subarray.

The Cypriot value of this division of the array $[1] [-3,7] [-6,2] [5] = 1 \cdot 1 + 2 \cdot (-3 + 7) + 3 \cdot (-6 + 2) + 4 \cdot 5 = 17$.

Theofanis is wondering what is the maximum Cypriot value of any division of the array.

$^{\dagger}$ An array $b$ is a subarray of an array $a$ if $b$ can be obtained from $a$ by deletion of several (possibly, zero or all) elements from the beginning and several (possibly, zero or all) elements from the end. In particular, an array is a subarray of itself.

## Input

The first line contains a single integer $t$ ($1 \le t \le 10^4$) — the number of test cases.

Each test case consists of two lines.

The first line of each test case contains a single integer $n$ ($1 \le n \le 10^{5}$) — the size of the array.

The second line contains $n$ integers $a_1, a_2, \ldots, a_n$ ($-10^8 \le a_i \le 10^{8}$) — the elements of the array.

It is guaranteed that the sum of $n$ over all test cases does not exceed $2 \cdot 10^{5}$.

## Output

For each test case, print one integer — the maximum Cypriot value of the array $a$.

## Note

In the first test case, to get the maximum Cypriot value we divide the array into $[1][-3][7][-6][2][5]$ which gives us: $\Sigma_{i=1}^{k} i \cdot \mathrm{sum}_i = 1 \cdot 1 + 2 \cdot (-3) + 3 \cdot 7 + 4 \cdot (-6) + 5 \cdot 2 + 6 \cdot 5 = 32$

Similarly, in the second test case we divide the array into $[2][9,-5,-3]$ which gives us $\Sigma_{i=1}^{k} i \cdot \mathrm{sum}_i = 1 \cdot 2 + 2 \cdot (9 + (-5) + (-3)) = 4$.

## Examples

*Example 1 — input:*
```
4
6
1 -3 7 -6 2 5
4
2 9 -5 -3
8
-3 -4 2 -5 1 10 17 23
1
830
```

*Example 1 — output:*
```
32
4
343
830
```
