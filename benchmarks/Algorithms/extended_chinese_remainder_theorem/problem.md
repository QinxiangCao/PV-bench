# P4777 — Extended Chinese Remainder Theorem

## Description

Given $n$ congruences

$$
x \equiv b_i \pmod {a_i},
$$

find the smallest nonnegative integer $x$ satisfying all of them. The moduli
$a_i$ are not required to be pairwise coprime. The input guarantees that a
solution exists.

## Input

The first line contains one integer $n$.

Each of the next $n$ lines contains two nonnegative integers $a_i$ and $b_i$,
representing the congruence $x \equiv b_i \pmod {a_i}$.

## Output

Print one integer: the smallest nonnegative solution $x$.

## Constraints

- $1 \le n \le 10^5$.
- $1 \le a_i \le 10^{12}$.
- $0 \le b_i \le 10^{12}$.
- The least common multiple of all $a_i$ does not exceed $10^{18}$.
- The input guarantees that the system has a solution.
- Intermediate multiplication may overflow a signed 64-bit integer unless it
  is handled carefully.

## Source

[Luogu P4777, "Extended Chinese Remainder Theorem"](https://www.luogu.com.cn/problem/P4777).
