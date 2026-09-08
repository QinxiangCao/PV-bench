# 1538/F — Interesting Function

*Rating:* 1500 · *Limits:* 2.0s, 256.0 MB · *Tags:* binary search, dp, math, number theory

## Description

You are given two integers $l$ and $r$, where $l < r$. We will add $1$ to $l$ until the result is equal to $r$. Thus, there will be exactly $r-l$ additions performed. For each such addition, let's look at the number of digits that will be changed after it.

For example:

- if $l=909$, then adding one will result in $910$ and $2$ digits will be changed;
- if you add one to $l=9$, the result will be $10$ and $2$ digits will also be changed;
- if you add one to $l=489999$, the result will be $490000$ and $5$ digits will be changed.

Changed digits always form a suffix of the result written in the decimal system.

Output the total number of changed digits, if you want to get $r$ from $l$, adding $1$ each time.

## Input

The first line contains an integer $t$ ($1 \le t \le 10^4$). Then $t$ test cases follow.

Each test case is characterized by two integers $l$ and $r$ ($1 \le l < r \le 10^9$).

## Output

For each test case, calculate the total number of changed digits if you want to get $r$ from $l$, adding one each time.

## Examples

*Example 1 — input:*
```
4
1 9
9 10
10 20
1 1000000000
```

*Example 1 — output:*
```
8
2
11
1111111110
```
