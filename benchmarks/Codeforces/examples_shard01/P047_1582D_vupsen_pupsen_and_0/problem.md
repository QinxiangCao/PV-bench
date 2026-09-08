# 1582/D — Vupsen, Pupsen and 0

*Rating:* 1600 · *Limits:* 1.0s, 256.0 MB · *Tags:* constructive algorithms, math

## Description

Vupsen and Pupsen were gifted an integer array. Since Vupsen doesn't like the number $0$, he threw away all numbers equal to $0$ from the array. As a result, he got an array $a$ of length $n$.

Pupsen, on the contrary, likes the number $0$ and he got upset when he saw the array without zeroes. To cheer Pupsen up, Vupsen decided to come up with another array $b$ of length $n$ such that $\sum_{i=1}^{n}a_i \cdot b_i=0$. Since Vupsen doesn't like number $0$, the array $b$ must not contain numbers equal to $0$. Also, the numbers in that array must not be huge, so the sum of their absolute values cannot exceed $10^9$. Please help Vupsen to find any such array $b$!

## Input

The first line contains a single integer $t$ ($1 \le t \le 100$) — the number of test cases. The next $2 \cdot t$ lines contain the description of test cases. The description of each test case consists of two lines.

The first line of each test case contains a single integer $n$ ($2 \le n \le 10^5$) — the length of the array.

The second line contains $n$ integers $a_1, a_2, \ldots, a_n$ ($-10^4 \le a_i \le 10^4$, $a_i \neq 0$) — the elements of the array $a$.

It is guaranteed that the sum of $n$ over all test cases does not exceed $2 \cdot 10^5$.

## Output

For each test case print $n$ integers $b_1, b_2, \ldots, b_n$ — elements of the array $b$ ($|b_1|+|b_2|+\ldots +|b_n| \le 10^9$, $b_i \neq 0$, $\sum_{i=1}^{n}a_i \cdot b_i=0$).

It can be shown that the answer always exists.

## Note

In the first test case, $5 \cdot 1 + 5 \cdot (-1)=5-5=0$. You could also print $3$ $-3$, for example, since $5 \cdot 3 + 5 \cdot (-3)=15-15=0$

In the second test case, $5 \cdot (-1) + (-2) \cdot 5 + 10 \cdot 1 + (-9) \cdot (-1) + 4 \cdot (-1)=-5-10+10+9-4=0$.

## Examples

*Example 1 — input:*
```
3
2
5 5
5
5 -2 10 -9 4
7
1 2 3 4 5 6 7
```

*Example 1 — output:*
```
1 -1
-1 5 1 -1 -1
-10 2 2 -3 5 -1 -1
```
