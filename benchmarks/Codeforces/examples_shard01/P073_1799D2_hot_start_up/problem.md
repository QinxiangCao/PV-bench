# 1799/D2 — Hot Start Up (hard version)

*Rating:* 2100 · *Limits:* 1.0s, 512.0 MB · *Tags:* data structures, dp

## Description

This is a hard version of the problem. The constraints of $t$, $n$, $k$ are the only difference between versions.

You have a device with two CPUs. You also have $k$ programs, numbered $1$ through $k$, that you can run on the CPUs.

The $i$-th program ($1 \le i \le k$) takes $cold_i$ seconds to run on some CPU. However, if the last program we ran on this CPU was also program $i$, it only takes $hot_i$ seconds ($hot_i \le cold_i$). Note that this only applies if we run program $i$ multiple times consecutively  — if we run program $i$, then some different program, then program $i$ again, it will take $cold_i$ seconds the second time.

You are given a sequence $a_1, a_2, \ldots, a_n$ of length $n$, consisting of integers from $1$ to $k$. You need to use your device to run programs $a_1, a_2, \ldots, a_n$ in sequence. For all $2 \le i \le n$, you cannot start running program $a_i$ until program $a_{i - 1}$ has completed.

Find the minimum amount of time needed to run all programs $a_1, a_2, \ldots, a_n$ in sequence.

## Input

Input consists of multiple test cases. The first line contains a single integer $t$, the number of test cases ($1 \le t \le 10^5$).

The first line of each test case contains $n$ and $k$ ($1 \le n, k \le 3 \cdot 10^5$).

The second line of each test case contains $n$ integers $a_1, a_2, \ldots, a_n$ ($1 \le a_i \le k$).

The third line of each test case contains $k$ integers $cold_1, cold_2, \ldots, cold_k$ ($1 \le cold_i \le 10^9$).

The fourth line of each test case contains $k$ integers $hot_1, hot_2, \ldots, hot_k$ ($1 \le hot_i \le cold_i$).

It is guaranteed the sum of $n$ and the sum of $k$ over all test cases do not exceed $3 \cdot 10^5$.

## Output

For each test case, print the minimum time needed to run all programs in the given order.

## Note

In the first test case, we can do the following:

- Run program $a_1 = 1$ on CPU $1$. It takes $cold_1 = 3$ seconds to run.
- Run program $a_2 = 2$ on CPU $2$. It takes $cold_2 = 2$ seconds to run.
- Run program $a_3 = 2$ on CPU $2$. The last program run on this CPU was also program $2$, so it takes $hot_2 = 1$ second to run.

In total, we need $3 + 2 + 1 = 6$ seconds to run them all. We can show this is optimal.

In the second test case, we can use do the following:

- Run program $a_1 = 1$ on CPU $1$. It takes $cold_1 = 5$ seconds to run.
- Run program $a_2 = 2$ on CPU $2$. It takes $cold_2 = 3$ seconds to run.
- Run program $a_3 = 1$ on CPU $1$. The last program run on this CPU was also program $1$, so it takes $hot_1 = 2$ seconds to run.
- Run program $a_4 = 2$ on CPU $2$. The last program run on this CPU was also program $2$, so it takes $hot_2 = 1$ second to run.

In total, we need $5 + 3 + 2 + 1 = 11$ seconds. We can show this is optimal.

## Examples

*Example 1 — input:*
```
9
3 2
1 2 2
3 2
2 1
4 2
1 2 1 2
5 3
2 1
4 3
1 2 3 1
100 100 100
1 1 1
5 2
2 1 2 1 1
65 45
54 7
5 3
1 3 2 1 2
2 2 2
1 1 1
5 1
1 1 1 1 1
1000000000
999999999
5 6
1 6 1 4 1
3 6 4 1 4 5
1 1 1 1 4 1
1 3
3
4 5 6
1 2 3
8 3
3 3 3 1 2 3 2 1
10 10 8
10 10 5
```

*Example 1 — output:*
```
6
11
301
225
8
4999999996
11
6
63
```
