# P1315 — Sightseeing Bus

## Description

A bus visits stations in order while passengers have arrival times, origins, and destinations. Up to $k$ units of travel time may be removed from road segments. Minimize the total passenger travel time.

## Input

The input gives $n$, $m$, $k$, the $n-1$ segment times, and $m$ passengers' arrival times, origins, and destinations.

## Output

Print the minimum possible sum of all passengers' travel times.

## Constraints

- $2 \le n \le 1000$ and $1 \le m \le 10000$.
- $0 \le k \le 100000$.
- Segment times lie in $[0,100]$; passenger times lie in $[0,100000]$.
- $1 \le origin_i < destination_i \le n$.

## Source

[Luogu P1315, Sightseeing Bus](https://www.luogu.com.cn/problem/P1315).
