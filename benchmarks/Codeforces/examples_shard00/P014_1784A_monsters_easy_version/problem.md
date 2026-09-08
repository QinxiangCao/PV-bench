# 1784/A — Monsters (easy version)

*Rating:* 1000 · *Limits:* 4.0s, 512.0 MB · *Tags:* brute force, greedy

## Description

This is the easy version of the problem. In this version, you only need to find the answer once. In this version, hacks are not allowed.

In a computer game, you are fighting against $n$ monsters. Monster number $i$ has $a_i$ health points, all $a_i$ are integers. A monster is alive while it has at least $1$ health point.

You can cast spells of two types:

1. Deal $1$ damage to any single alive monster of your choice.
2. Deal $1$ damage to all alive monsters. If at least one monster dies (ends up with $0$ health points) as a result of this action, then repeat it (and keep repeating while at least one monster dies every time).

Dealing $1$ damage to a monster reduces its health by $1$.

Spells of type 1 can be cast any number of times, while a spell of type 2 can be cast at most once during the game.

What is the smallest number of times you need to cast spells of type 1 to kill all monsters?

## Input

Each test contains multiple test cases. The first line contains the number of test cases $t$ ($1 \le t \le 10^4$). The description of the test cases follows.

Each test case consists of two lines. The first line contains a single integer $n$ ($1 \le n \le 2 \cdot 10^5$) — the number of monsters.

The second line contains $n$ integers $a_1, a_2, \ldots, a_n$ ($1 \le a_i \le n$) — monsters' health points.

It is guaranteed that the sum of $n$ over all test cases does not exceed $2 \cdot 10^5$.

## Output

For each test case, print a single integer — the smallest number of times you need to cast spells of type 1 to kill all monsters.

## Note

In the first test case, the initial health points of the monsters are $[3, 1, 2]$. It is enough to cast a spell of type 2:

- Monsters' health points change to $[2, 0, 1]$. Since monster number $2$ dies, the spell is repeated.
- Monsters' health points change to $[1, 0, 0]$. Since monster number $3$ dies, the spell is repeated.
- Monsters' health points change to $[0, 0, 0]$. Since monster number $1$ dies, the spell is repeated.
- Monsters' health points change to $[0, 0, 0]$.

Since it is possible to use no spells of type 1 at all, the answer is $0$.

In the second test case, the initial health points of the monsters are $[4, 1, 5, 4, 1, 1]$. Here is one of the optimal action sequences:

- Using a spell of type 1, deal $1$ damage to monster number $1$. Monsters' health points change to $[3, 1, 5, 4, 1, 1]$.
- Using a spell of type 1, deal $1$ damage to monster number $4$. Monsters' health points change to $[3, 1, 5, 3, 1, 1]$.
- Using a spell of type 1, deal $1$ damage to monster number $4$ again. Monsters' health points change to $[3, 1, 5, 2, 1, 1]$.
- Use a spell of type 2:  Monsters' health points change to $[2, 0, 4, 1, 0, 0]$. Since monsters number $2$, $5$, and $6$ die, the spell is repeated.  Monsters' health points change to $[1, 0, 3, 0, 0, 0]$. Since monster number $4$ dies, the spell is repeated.  Monsters' health points change to $[0, 0, 2, 0, 0, 0]$. Since monster number $1$ dies, the spell is repeated.  Monsters' health points change to $[0, 0, 1, 0, 0, 0]$.
- Using a spell of type 1, deal $1$ damage to monster number $3$. Monsters' health points change to $[0, 0, 0, 0, 0, 0]$.

Spells of type 1 are cast $4$ times in total. It can be shown that this is the smallest possible number.

## Examples

*Example 1 — input:*
```
2
3
3 1 2
6
4 1 5 4 1 1
```

*Example 1 — output:*
```
0
4
```
