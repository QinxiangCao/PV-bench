# 1594/D — The Number of Imposters

*Rating:* 1700 · *Limits:* 3.0s, 256.0 MB · *Tags:* constructive algorithms, dfs and similar, dp, dsu, graphs

## Description

Theofanis started playing the new online game called "Among them". However, he always plays with Cypriot players, and they all have the same name: "Andreas" (the most common name in Cyprus).

In each game, Theofanis plays with $n$ other players. Since they all have the same name, they are numbered from $1$ to $n$.

The players write $m$ comments in the chat. A comment has the structure of "$i$ $j$ $c$" where $i$ and $j$ are two distinct integers and $c$ is a string ($1 \le i, j \le n$; $i \neq j$; $c$ is either imposter or crewmate). The comment means that player $i$ said that player $j$ has the role $c$.

An imposter always lies, and a crewmate always tells the truth.

Help Theofanis find the maximum possible number of imposters among all the other Cypriot players, or determine that the comments contradict each other (see the notes for further explanation).

Note that each player has exactly one role: either imposter or crewmate.

## Input

The first line contains a single integer $t$ ($1 \le t \le 10^4$) — the number of test cases. Description of each test case follows.

The first line of each test case contains two integers $n$ and $m$ ($1 \le n \le 2 \cdot 10^5$; $0 \le m \le 5 \cdot 10^5$) — the number of players except Theofanis and the number of comments.

Each of the next $m$ lines contains a comment made by the players of the structure "$i$ $j$ $c$" where $i$ and $j$ are two distinct integers and $c$ is a string ($1 \le i, j \le n$; $i \neq j$; $c$ is either imposter or crewmate).

There can be multiple comments for the same pair of $(i, j)$.

It is guaranteed that the sum of all $n$ does not exceed $2 \cdot 10^5$ and the sum of all $m$ does not exceed $5 \cdot 10^5$.

## Output

For each test case, print one integer — the maximum possible number of imposters. If the comments contradict each other, print $-1$.

## Note

In the first test case, imposters can be Andreas $2$ and $3$.

In the second test case, imposters can be Andreas $1$, $2$, $3$ and $5$.

In the third test case, comments contradict each other. This is because player $1$ says that player $2$ is an imposter, and player $2$ says that player $1$ is a crewmate. If player $1$ is a crewmate, then he must be telling the truth, so player $2$ must be an imposter. But if player $2$ is an imposter then he must be lying, so player $1$ can't be a crewmate. Contradiction.

## Examples

*Example 1 — input:*
```
5
3 2
1 2 imposter
2 3 crewmate
5 4
1 3 crewmate
2 5 crewmate
2 4 imposter
3 4 imposter
2 2
1 2 imposter
2 1 crewmate
3 5
1 2 imposter
1 2 imposter
3 2 crewmate
3 2 crewmate
1 3 imposter
5 0
```

*Example 1 — output:*
```
2
4
-1
2
5
```
