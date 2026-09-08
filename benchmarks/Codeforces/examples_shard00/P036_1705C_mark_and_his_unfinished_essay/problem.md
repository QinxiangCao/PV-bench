# 1705/C — Mark and His Unfinished Essay

*Rating:* 1400 · *Limits:* 2.0s, 256.0 MB · *Tags:* brute force, implementation

## Description

One night, Mark realized that there is an essay due tomorrow. He hasn't written anything yet, so Mark decided to randomly copy-paste substrings from the prompt to make the essay.

More formally, the prompt is a string $s$ of initial length $n$. Mark will perform the copy-pasting operation $c$ times. Each operation is described by two integers $l$ and $r$, which means that Mark will append letters $s_l s_{l+1} \ldots s_r$ to the end of string $s$. Note that the length of $s$ increases after this operation.

Of course, Mark needs to be able to see what has been written. After copying, Mark will ask $q$ queries: given an integer $k$, determine the $k$-th letter of the final string $s$.

## Input

The first line contains a single integer $t$ ($1\leq t\leq 1000$) — the number of test cases.

The first line of each test case contains three integers $n$, $c$, and $q$ ($1\leq n\leq 2\cdot 10^5$, $1\leq c\leq 40$, and $1\leq q\leq 10^4$) — the length of the initial string $s$, the number of copy-pasting operations, and the number of queries, respectively.

The second line of each test case contains a single string $s$ of length $n$. It is guaranteed that $s$ only contains lowercase English letters.

The following $c$ lines describe the copy-pasting operation. Each line contains two integers $l$ and $r$ ($1\leq l\leq r\leq 10^{18}$). It is also guaranteed that $r$ does not exceed the current length of $s$.

The last $q$ lines of each test case describe the queries. Each line contains a single integer $k$ ($1\leq k\leq 10^{18}$). It is also guaranteed that $k$ does not exceed the final length of $s$.

It is guaranteed that the sum of $n$ and $q$ across all test cases does not exceed $2\cdot 10^5$ and $10^4$, respectively.

## Output

For each query, print the $k$-th letter of the final string $s$.

## Note

In the first test case, the copy-paste process is as follows.

- The first step is pasting string $\texttt{mark}$ at the end, yielding the string $\texttt{mark}\color{red}{\texttt{mark}}$.
- The second step is pasting string $\texttt{mar}$ at the end, yielding the string $\texttt{markmark}\color{red}{\texttt{mar}}$.
- The third step is pasting string $\texttt{rkmark}$ at the end, yielding the string $\texttt{markmarkmar}\color{red}{\texttt{rkmark}}$.

In the second test case, the copy-paste process is as follows.

- The first step is pasting string $\texttt{re}$ at the end, yielding the string $\texttt{creamii}\color{red}{\texttt{re}}$.
- The second step is pasting string $\texttt{ea}$ at the end, yielding the string $\texttt{creamiire}\color{red}{\texttt{ea}}$.
- The third step is pasting string $\texttt{reamiire}$ at the end, yielding the string $\texttt{creamiireea}\color{red}{\texttt{reamiire}}$.

## Examples

*Example 1 — input:*
```
2
4 3 3
mark
1 4
5 7
3 8
1
10
12
7 3 3
creamii
2 3
3 4
2 9
9
11
12
```

*Example 1 — output:*
```
m
a
r
e
a
r
```
