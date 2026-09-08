# 498/D — Traffic Jams in the Land

*Rating:* 2400 · *Limits:* 2.0s, 256.0 MB · *Tags:* data structures, dp, number theory

## Description

Some country consists of (n + 1) cities, located along a straight highway. Let's number the cities with consecutive integers from 1 to n + 1 in the order they occur along the highway. Thus, the cities are connected by n segments of the highway, the i-th segment connects cities number i and i + 1. Every segment of the highway is associated with a positive integer ai > 1 — the period of traffic jams appearance on it.

In order to get from city x to city y (x < y), some drivers use the following tactics.

Initially the driver is in city x and the current time t equals zero. Until the driver arrives in city y, he perfors the following actions:

- if the current time t is a multiple of ax, then the segment of the highway number x is now having traffic problems and the driver stays in the current city for one unit of time (formally speaking, we assign t = t + 1);
- if the current time t is not a multiple of ax, then the segment of the highway number x is now clear and that's why the driver uses one unit of time to move to city x + 1 (formally, we assign t = t + 1 and x = x + 1).

You are developing a new traffic control system. You want to consecutively process q queries of two types:

1. determine the final value of time t after the ride from city x to city y (x < y) assuming that we apply the tactics that is described above. Note that for each query t is being reset to 0.
2. replace the period of traffic jams appearing on the segment number x by value y (formally, assign ax = y).

Write a code that will effectively process the queries given above.

## Input

The first line contains a single integer n (1 ≤ n ≤ 105) — the number of highway segments that connect the n + 1 cities.

The second line contains n integers a1, a2, ..., an (2 ≤ ai ≤ 6) — the periods of traffic jams appearance on segments of the highway.

The next line contains a single integer q (1 ≤ q ≤ 105) — the number of queries to process.

The next q lines contain the descriptions of the queries in the format c, x, y (c — the query type).

If c is character 'A', then your task is to process a query of the first type. In this case the following constraints are satisfied: 1 ≤ x < y ≤ n + 1.

If c is character 'C', then you need to process a query of the second type. In such case, the following constraints are satisfied: 1 ≤ x ≤ n, 2 ≤ y ≤ 6.

## Output

For each query of the first type output a single integer — the final value of time t after driving from city x to city y. Process the queries in the order in which they are given in the input.

## Examples

*Example 1 — input:*
```
10
2 5 3 2 3 5 3 4 2 4
10
C 10 6
A 2 6
A 1 3
C 3 4
A 3 11
A 4 9
A 5 6
C 7 3
A 8 10
A 2 5
```

*Example 1 — output:*
```
5
3
14
6
2
4
4
```
