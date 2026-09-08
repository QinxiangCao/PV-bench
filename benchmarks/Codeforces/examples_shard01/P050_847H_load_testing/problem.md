# 847/H — Load Testing

*Rating:* 1600 · *Limits:* 1.0s, 256.0 MB · *Tags:* greedy

## Description

Polycarp plans to conduct a load testing of its new project Fakebook. He already agreed with his friends that at certain points in time they will send requests to Fakebook. The load testing will last n minutes and in the i-th minute friends will send ai requests.

Polycarp plans to test Fakebook under a special kind of load. In case the information about Fakebook gets into the mass media, Polycarp hopes for a monotone increase of the load, followed by a monotone decrease of the interest to the service. Polycarp wants to test this form of load.

Your task is to determine how many requests Polycarp must add so that before some moment the load on the server strictly increases and after that moment strictly decreases. Both the increasing part and the decreasing part can be empty (i. e. absent). The decrease should immediately follow the increase. In particular, the load with two equal neigbouring values is unacceptable.

For example, if the load is described with one of the arrays [1, 2, 8, 4, 3], [1, 3, 5] or [10], then such load satisfies Polycarp (in each of the cases there is an increasing part, immediately followed with a decreasing part). If the load is described with one of the arrays [1, 2, 2, 1], [2, 1, 2] or [10, 10], then such load does not satisfy Polycarp.

Help Polycarp to make the minimum number of additional requests, so that the resulting load satisfies Polycarp. He can make any number of additional requests at any minute from 1 to n.

## Input

The first line contains a single integer n (1 ≤ n ≤ 100 000) — the duration of the load testing.

The second line contains n integers a1, a2, ..., an (1 ≤ ai ≤ 109), where ai is the number of requests from friends in the i-th minute of the load testing.

## Output

Print the minimum number of additional requests from Polycarp that would make the load strictly increasing in the beginning and then strictly decreasing afterwards.

## Note

In the first example Polycarp must make two additional requests in the third minute and four additional requests in the fourth minute. So the resulting load will look like: [1, 4, 5, 6, 5]. In total, Polycarp will make 6 additional requests.

In the second example it is enough to make one additional request in the third minute, so the answer is 1.

In the third example the load already satisfies all conditions described in the statement, so the answer is 0.

## Examples

*Example 1 — input:*
```
5
1 4 3 2 5
```

*Example 1 — output:*
```
6
```

*Example 2 — input:*
```
5
1 2 2 2 1
```

*Example 2 — output:*
```
1
```

*Example 3 — input:*
```
7
10 20 40 50 70 90 30
```

*Example 3 — output:*
```
0
```
