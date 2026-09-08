# 1316/E — Team Building

*Rating:* 2300 · *Limits:* 3.0s, 256.0 MB · *Tags:* bitmasks, dp, greedy, sortings

## Description

Alice, the president of club FCB, wants to build a team for the new volleyball tournament. The team should consist of $p$ players playing in $p$ different positions. She also recognizes the importance of audience support, so she wants to select $k$ people as part of the audience.

There are $n$ people in Byteland. Alice needs to select exactly $p$ players, one for each position, and exactly $k$ members of the audience from this pool of $n$ people. Her ultimate goal is to maximize the total strength of the club.

The $i$-th of the $n$ persons has an integer $a_{i}$ associated with him — the strength he adds to the club if he is selected as a member of the audience.

For each person $i$ and for each position $j$, Alice knows $s_{i, j}$  — the strength added by the $i$-th person to the club if he is selected to play in the $j$-th position.

Each person can be selected at most once as a player or a member of the audience. You have to choose exactly one player for each position.

Since Alice is busy, she needs you to help her find the maximum possible strength of the club that can be achieved by an optimal choice of players and the audience.

## Input

The first line contains $3$ integers $n,p,k$ ($2 \leq n \leq 10^{5}, 1 \leq p \leq 7, 1 \le k, p+k \le n$).

The second line contains $n$ integers $a_{1},a_{2},\ldots,a_{n}$. ($1 \leq a_{i} \leq 10^{9}$).

The $i$-th of the next $n$ lines contains $p$ integers $s_{i, 1}, s_{i, 2}, \dots, s_{i, p}$. ($1 \leq s_{i,j} \leq 10^{9}$)

## Output

Print a single integer ${res}$  — the maximum possible strength of the club.

## Note

In the first sample, we can select person $1$ to play in the $1$-st position and persons $2$ and $3$ as audience members. Then the total strength of the club will be equal to $a_{2}+a_{3}+s_{1,1}$.

## Examples

*Example 1 — input:*
```
4 1 2
1 16 10 3
18
19
13
15
```

*Example 1 — output:*
```
44
```

*Example 2 — input:*
```
6 2 3
78 93 9 17 13 78
80 97
30 52
26 17
56 68
60 36
84 55
```

*Example 2 — output:*
```
377
```

*Example 3 — input:*
```
3 2 1
500 498 564
100002 3
422332 2
232323 1
```

*Example 3 — output:*
```
422899
```
