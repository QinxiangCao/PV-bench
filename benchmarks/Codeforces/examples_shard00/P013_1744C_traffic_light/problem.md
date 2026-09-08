# 1744/C — Traffic Light

*Rating:* 1000 · *Limits:* 1.0s, 256.0 MB · *Tags:* binary search, implementation, two pointers

## Description

You find yourself on an unusual crossroad with a weird traffic light. That traffic light has three possible colors: red (r), yellow (y), green (g). It is known that the traffic light repeats its colors every $n$ seconds and at the $i$-th second the color $s_i$ is on.

That way, the order of the colors is described by a string. For example, if $s=$"rggry", then the traffic light works as the following: red-green-green-red-yellow-red-green-green-red-yellow- ... and so on.

More formally, you are given a string $s_1, s_2, \ldots, s_n$ of length $n$. At the first second the color $s_1$ is on, at the second — $s_2$, ..., at the $n$-th second the color $s_n$ is on, at the $n + 1$-st second the color $s_1$ is on and so on.

You need to cross the road and that can only be done when the green color is on.

You know which color is on the traffic light at the moment, but you don't know the current moment of time. You need to find the minimum amount of time in which you are guaranteed to cross the road.

You can assume that you cross the road immediately.

For example, with $s=$"rggry" and the current color r there are two options: either the green color will be on after $1$ second, or after $3$. That way, the answer is equal to $3$ — that is the number of seconds that we are guaranteed to cross the road, if the current color is r.

## Input

The first line contains a single integer $t$ $(1 \leq t \leq 10^4$) — the number of test cases.

Then the description of the test cases follows.

The first line of each test case contains an integer $n$ and a symbol $c$ ($1 \leq n \leq 2 \cdot 10^5$, $c$ is one of allowed traffic light colors r, y or g)— the length of the string $s$ and the current color of the traffic light.

The second line of each test case contains a string $s$ of the length $n$, consisting of the letters r, y and g.

It is guaranteed that the symbol g is in the string $s$ and the symbol $c$ is in the string $s$.

It is guaranteed, that the sum of $n$ over all test cases does not exceed $2\cdot10^5$.

## Output

For each test case output the minimal number of second in which you are guaranteed to cross the road.

## Note

The first test case is explained in the statement.

In the second test case the green color is on so you can cross the road immediately.

In the third test case, if the red color was on at the second second, then we would wait for the green color for one second, and if the red light was on at the first second, then we would wait for the green light for two seconds.

In the fourth test case the longest we would wait for the green color is if we wait for it starting from the fifth second.

## Examples

*Example 1 — input:*
```
6
5 r
rggry
1 g
g
3 r
rrg
5 y
yrrgy
7 r
rgrgyrg
9 y
rrrgyyygy
```

*Example 1 — output:*
```
3
0
2
4
1
4
```
